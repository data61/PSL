(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Typing\<close>
theory OCL_Typing
  imports OCL_Object_Model "HOL-Library.Transitive_Closure_Table"
begin

text \<open>
  The following rules are more restrictive than rules given in
  the OCL specification. This allows one to identify more errors
  in expressions. However, these restrictions may be revised if necessary.
  Perhaps some of them could be separated and should cause warnings
  instead of errors.\<close>

(*** Operations Typing ******************************************************)

section \<open>Operations Typing\<close>

subsection \<open>Metaclass Operations\<close>

text \<open>
  All basic types in the theory are either nullable or non-nullable.
  For example, instead of @{text Boolean} type we have two types:
  @{text "Boolean[1]"} and @{text "Boolean[?]"}.
  The @{text "allInstances()"} operation is extended accordingly:\<close>

text \<open>
\<^verbatim>\<open>Boolean[1].allInstances() = Set{true, false}
Boolean[?].allInstances() = Set{true, false, null}\<close>\<close>

inductive mataop_type where
  "mataop_type \<tau> AllInstancesOp (Set \<tau>)"

subsection \<open>Type Operations\<close>

text \<open>
  At first we decided to allow casting only to subtypes.
  However sometimes it is necessary to cast expressions to supertypes,
  for example, to access overridden attributes of a supertype.
  So we allow casting to subtypes and supertypes.
  Casting to other types is meaningless.\<close>

text \<open>
  According to the Section 7.4.7 of the OCL specification
  @{text "oclAsType()"} can be applied to collections as well as
  to single values. I guess we can allow @{text "oclIsTypeOf()"}
  and @{text "oclIsKindOf()"} for collections too.\<close>

text \<open>
  Please take a note that the following expressions are prohibited,
  because they always return true or false:\<close>

text \<open>
\<^verbatim>\<open>1.oclIsKindOf(OclAny[?])
1.oclIsKindOf(String[1])\<close>\<close>

text \<open>
  Please take a note that:\<close>

text \<open>
\<^verbatim>\<open>Set{1,2,null,'abc'}->selectByKind(Integer[1]) = Set{1,2}
Set{1,2,null,'abc'}->selectByKind(Integer[?]) = Set{1,2,null}\<close>\<close>

text \<open>
  The following expressions are prohibited, because they always
  returns either the same or empty collections:\<close>

text \<open>
\<^verbatim>\<open>Set{1,2,null,'abc'}->selectByKind(OclAny[?])
Set{1,2,null,'abc'}->selectByKind(Collection(Boolean[1]))\<close>\<close>

inductive typeop_type where
  "\<sigma> < \<tau> \<or> \<tau> < \<sigma> \<Longrightarrow>
   typeop_type DotCall OclAsTypeOp \<tau> \<sigma> \<sigma>"

| "\<sigma> < \<tau> \<Longrightarrow>
   typeop_type DotCall OclIsTypeOfOp \<tau> \<sigma> Boolean[1]"
| "\<sigma> < \<tau> \<Longrightarrow>
   typeop_type DotCall OclIsKindOfOp \<tau> \<sigma> Boolean[1]"

| "element_type \<tau> \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow>
   update_element_type \<tau> \<sigma> \<upsilon> \<Longrightarrow>
   typeop_type ArrowCall SelectByKindOp \<tau> \<sigma> \<upsilon>"

| "element_type \<tau> \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow>
   update_element_type \<tau> \<sigma> \<upsilon> \<Longrightarrow>
   typeop_type ArrowCall SelectByTypeOp \<tau> \<sigma> \<upsilon>"

subsection \<open>OclSuper Operations\<close>

text \<open>
  It makes sense to compare values only with compatible types.\<close>

(* We have to specify the predicate type explicitly to let
   a generated code work *)
inductive super_binop_type
    :: "super_binop \<Rightarrow> ('a :: order) type \<Rightarrow> 'a type \<Rightarrow> 'a type \<Rightarrow> bool" where
  "\<tau> \<le> \<sigma> \<or> \<sigma> < \<tau> \<Longrightarrow>
   super_binop_type EqualOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<le> \<sigma> \<or> \<sigma> < \<tau> \<Longrightarrow>
   super_binop_type NotEqualOp \<tau> \<sigma> Boolean[1]"

subsection \<open>OclAny Operations\<close>

text \<open>
  The OCL specification defines @{text "toString()"} operation
  only for boolean and numeric types. However, I guess it is a good
  idea to define it once for all basic types. Maybe it should be defined
  for collections as well.\<close>

inductive any_unop_type where
  "\<tau> \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclAsSetOp \<tau> (Set (to_required_type \<tau>))"
| "\<tau> \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclIsNewOp \<tau> Boolean[1]"
| "\<tau> \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclIsUndefinedOp \<tau> Boolean[1]"
| "\<tau> \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclIsInvalidOp \<tau> Boolean[1]"
| "\<tau> \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclLocaleOp \<tau> String[1]"
| "\<tau> \<le> OclAny[?] \<Longrightarrow>
   any_unop_type ToStringOp \<tau> String[1]"

subsection \<open>Boolean Operations\<close>

text \<open>
  Please take a note that:\<close>

text \<open>
\<^verbatim>\<open>true or false : Boolean[1]
true and null : Boolean[?]
null and null : OclVoid[?]\<close>\<close>

inductive boolean_unop_type where
  "\<tau> \<le> Boolean[?] \<Longrightarrow>
   boolean_unop_type NotOp \<tau> \<tau>"

inductive boolean_binop_type where
  "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> \<le> Boolean[?] \<Longrightarrow>
   boolean_binop_type AndOp \<tau> \<sigma> \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> \<le> Boolean[?] \<Longrightarrow>
   boolean_binop_type OrOp \<tau> \<sigma> \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> \<le> Boolean[?] \<Longrightarrow>
   boolean_binop_type XorOp \<tau> \<sigma> \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> \<le> Boolean[?] \<Longrightarrow>
   boolean_binop_type ImpliesOp \<tau> \<sigma> \<rho>"

subsection \<open>Numeric Operations\<close>

text \<open>
  The expression @{text "1 + null"} is not well-typed.
  Nullable numeric values should be converted to non-nullable ones.
  This is a significant difference from the OCL specification.\<close>

text \<open>
  Please take a note that many operations automatically casts
  unlimited naturals to integers.\<close>

text \<open>
  The difference between @{text "oclAsType(Integer)"} and
  @{text "toInteger()"} for unlimited naturals is unclear.\<close>

inductive numeric_unop_type where
  "\<tau> = Real[1] \<Longrightarrow>
   numeric_unop_type UMinusOp \<tau> Real[1]"
| "\<tau> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   numeric_unop_type UMinusOp \<tau> Integer[1]"

| "\<tau> = Real[1] \<Longrightarrow>
   numeric_unop_type AbsOp \<tau> Real[1]"
| "\<tau> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   numeric_unop_type AbsOp \<tau> Integer[1]"

| "\<tau> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_unop_type FloorOp \<tau> Integer[1]"
| "\<tau> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_unop_type RoundOp \<tau> Integer[1]"

| "\<tau> = UnlimitedNatural[1] \<Longrightarrow>
   numeric_unop_type numeric_unop.ToIntegerOp \<tau> Integer[1]"

inductive numeric_binop_type where
  "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type PlusOp \<tau> \<sigma> \<rho>"

| "\<tau> \<squnion> \<sigma> = Real[1] \<Longrightarrow>
   numeric_binop_type MinusOp \<tau> \<sigma> Real[1]"
| "\<tau> \<squnion> \<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   numeric_binop_type MinusOp \<tau> \<sigma> Integer[1]"

| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type MultOp \<tau> \<sigma> \<rho>"

| "\<tau> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type DivideOp \<tau> \<sigma> Real[1]"

| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   numeric_binop_type DivOp \<tau> \<sigma> \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   numeric_binop_type ModOp \<tau> \<sigma> \<rho>"

| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type MaxOp \<tau> \<sigma> \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type MinOp \<tau> \<sigma> \<rho>"

| "\<tau> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type numeric_binop.LessOp \<tau> \<sigma> Boolean[1]"
| "\<tau> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type numeric_binop.LessEqOp \<tau> \<sigma> Boolean[1]"
| "\<tau> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type numeric_binop.GreaterOp \<tau> \<sigma> Boolean[1]"
| "\<tau> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type numeric_binop.GreaterEqOp \<tau> \<sigma> Boolean[1]"

subsection \<open>String Operations\<close>

inductive string_unop_type where
  "string_unop_type SizeOp String[1] Integer[1]"
| "string_unop_type CharactersOp String[1] (Sequence String[1])"
| "string_unop_type ToUpperCaseOp String[1] String[1]"
| "string_unop_type ToLowerCaseOp String[1] String[1]"
| "string_unop_type ToBooleanOp String[1] Boolean[1]"
| "string_unop_type ToIntegerOp String[1] Integer[1]"
| "string_unop_type ToRealOp String[1] Real[1]"

inductive string_binop_type where
  "string_binop_type ConcatOp String[1] String[1] String[1]"
| "string_binop_type EqualsIgnoreCaseOp String[1] String[1] Boolean[1]"
| "string_binop_type LessOp String[1] String[1] Boolean[1]"
| "string_binop_type LessEqOp String[1] String[1] Boolean[1]"
| "string_binop_type GreaterOp String[1] String[1] Boolean[1]"
| "string_binop_type GreaterEqOp String[1] String[1] Boolean[1]"
| "string_binop_type IndexOfOp String[1] String[1] Integer[1]"
| "\<tau> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   string_binop_type AtOp String[1] \<tau> String[1]"

inductive string_ternop_type where
  "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   \<rho> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   string_ternop_type SubstringOp String[1] \<sigma> \<rho> String[1]"

subsection \<open>Collection Operations\<close>

text \<open>
  Please take a note, that @{text "flatten()"} preserves a collection kind.\<close>

inductive collection_unop_type where
  "element_type \<tau> _ \<Longrightarrow>
   collection_unop_type CollectionSizeOp \<tau> Integer[1]"
| "element_type \<tau> _ \<Longrightarrow>
   collection_unop_type IsEmptyOp \<tau> Boolean[1]"
| "element_type \<tau> _ \<Longrightarrow>
   collection_unop_type NotEmptyOp \<tau> Boolean[1]"

| "element_type \<tau> \<sigma> \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   collection_unop_type CollectionMaxOp \<tau> \<sigma>"
| "element_type \<tau> \<sigma> \<Longrightarrow> operation \<sigma> STR ''max'' [\<sigma>] oper \<Longrightarrow>
   collection_unop_type CollectionMaxOp \<tau> \<sigma>"

| "element_type \<tau> \<sigma> \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   collection_unop_type CollectionMinOp \<tau> \<sigma>"
| "element_type \<tau> \<sigma> \<Longrightarrow> operation \<sigma> STR ''min'' [\<sigma>] oper \<Longrightarrow>
   collection_unop_type CollectionMinOp \<tau> \<sigma>"

| "element_type \<tau> \<sigma> \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   collection_unop_type SumOp \<tau> \<sigma>"
| "element_type \<tau> \<sigma> \<Longrightarrow> operation \<sigma> STR ''+'' [\<sigma>] oper \<Longrightarrow>
   collection_unop_type SumOp \<tau> \<sigma>"

| "element_type \<tau> \<sigma> \<Longrightarrow>
   collection_unop_type AsSetOp \<tau> (Set \<sigma>)"
| "element_type \<tau> \<sigma> \<Longrightarrow>
   collection_unop_type AsOrderedSetOp \<tau> (OrderedSet \<sigma>)"
| "element_type \<tau> \<sigma> \<Longrightarrow>
   collection_unop_type AsBagOp \<tau> (Bag \<sigma>)"
| "element_type \<tau> \<sigma> \<Longrightarrow>
   collection_unop_type AsSequenceOp \<tau> (Sequence \<sigma>)"

| "update_element_type \<tau> (to_single_type \<tau>) \<sigma> \<Longrightarrow>
   collection_unop_type FlattenOp \<tau> \<sigma>"

| "collection_unop_type FirstOp (OrderedSet \<tau>) \<tau>"
| "collection_unop_type FirstOp (Sequence \<tau>) \<tau>"
| "collection_unop_type LastOp (OrderedSet \<tau>) \<tau>"
| "collection_unop_type LastOp (Sequence \<tau>) \<tau>"
| "collection_unop_type ReverseOp (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "collection_unop_type ReverseOp (Sequence \<tau>) (Sequence \<tau>)"

text \<open>
  Please take a note that if both arguments are collections,
  then an element type of the resulting collection is a super type
  of element types of orginal collections. However for single-valued
  operations (@{text "append()"}, @{text "insertAt()"}, ...)
  this behavior looks undesirable. So we restrict such arguments
  to have a subtype of the collection element type.\<close>

text \<open>
  Please take a note that we allow the following expressions:\<close>

text \<open>
\<^verbatim>\<open>let nullable_value : Integer[?] = null in
Sequence{1..3}->inculdes(nullable_value) and
Sequence{1..3}->inculdes(null) and
Sequence{1..3}->inculdesAll(Set{1,null})\<close>\<close>

text \<open>
  The OCL specification defines @{text "including()"} and
  @{text "excluding()"} operations for the @{text Sequence} type
  but does not define them for the @{text OrderedSet} type.
  We define them for all collection types.

  It is a good idea to prohibit including of values that
  do not conform to a collection element type.
  However we do not restrict it.

  At first we defined the following typing rules for the
  @{text "excluding()"} operation:

{\isacharbar}\ {\isachardoublequoteopen}element{\isacharunderscore}type\ {\isasymtau}\ {\isasymrho}\ {\isasymLongrightarrow}\ {\isasymsigma}\ {\isasymle}\ {\isasymrho}\ {\isasymLongrightarrow}\ {\isasymsigma}\ {\isasymnoteq}\ OclVoid{\isacharbrackleft}{\isacharquery}{\isacharbrackright}\ {\isasymLongrightarrow}\isanewline
\ \ \ collection{\isacharunderscore}binop{\isacharunderscore}type\ ExcludingOp\ {\isasymtau}\ {\isasymsigma}\ {\isasymtau}{\isachardoublequoteclose}\isanewline
{\isacharbar}\ {\isachardoublequoteopen}element{\isacharunderscore}type\ {\isasymtau}\ {\isasymrho}\ {\isasymLongrightarrow}\ {\isasymsigma}\ {\isasymle}\ {\isasymrho}\ {\isasymLongrightarrow}\ {\isasymsigma}\ {\isacharequal}\ OclVoid{\isacharbrackleft}{\isacharquery}{\isacharbrackright}\ {\isasymLongrightarrow}\isanewline
\ \ \ update{\isacharunderscore}element{\isacharunderscore}type\ {\isasymtau}\ {\isacharparenleft}to{\isacharunderscore}required{\isacharunderscore}type\ {\isasymrho}{\isacharparenright}\ {\isasymupsilon}\ {\isasymLongrightarrow}\isanewline
\ \ \ collection{\isacharunderscore}binop{\isacharunderscore}type\ ExcludingOp\ {\isasymtau}\ {\isasymsigma}\ {\isasymupsilon}{\isachardoublequoteclose}\isanewline

  This operation could play a special role in a definition
  of safe navigation operations:\<close>

text \<open>
\<^verbatim>\<open>Sequence{1,2,null}->exculding(null) : Integer[1]\<close>\<close>

text \<open>
  However it is more natural to use a @{text "selectByKind(T[1])"}
  operation instead.\<close>

inductive collection_binop_type where
  "element_type \<tau> \<rho> \<Longrightarrow> \<sigma> \<le> to_optional_type_nested \<rho> \<Longrightarrow>
   collection_binop_type IncludesOp \<tau> \<sigma> Boolean[1]"
| "element_type \<tau> \<rho> \<Longrightarrow> \<sigma> \<le> to_optional_type_nested \<rho> \<Longrightarrow>
   collection_binop_type ExcludesOp \<tau> \<sigma> Boolean[1]"
| "element_type \<tau> \<rho> \<Longrightarrow> \<sigma> \<le> to_optional_type_nested \<rho> \<Longrightarrow>
   collection_binop_type CountOp \<tau> \<sigma> Integer[1]"

| "element_type \<tau> \<rho> \<Longrightarrow> element_type \<sigma> \<upsilon> \<Longrightarrow> \<upsilon> \<le> to_optional_type_nested \<rho> \<Longrightarrow>
   collection_binop_type IncludesAllOp \<tau> \<sigma> Boolean[1]"
| "element_type \<tau> \<rho> \<Longrightarrow> element_type \<sigma> \<upsilon> \<Longrightarrow> \<upsilon> \<le> to_optional_type_nested \<rho> \<Longrightarrow>
   collection_binop_type ExcludesAllOp \<tau> \<sigma> Boolean[1]"

| "element_type \<tau> \<rho> \<Longrightarrow> element_type \<sigma> \<upsilon> \<Longrightarrow>
   collection_binop_type ProductOp \<tau> \<sigma>
      (Set (Tuple (fmap_of_list [(STR ''first'', \<rho>), (STR ''second'', \<upsilon>)])))"

| "collection_binop_type UnionOp (Set \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type UnionOp (Set \<tau>) (Bag \<sigma>) (Bag (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type UnionOp (Bag \<tau>) (Set \<sigma>) (Bag (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type UnionOp (Bag \<tau>) (Bag \<sigma>) (Bag (\<tau> \<squnion> \<sigma>))"

| "collection_binop_type IntersectionOp (Set \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type IntersectionOp (Set \<tau>) (Bag \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type IntersectionOp (Bag \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type IntersectionOp (Bag \<tau>) (Bag \<sigma>) (Bag (\<tau> \<squnion> \<sigma>))"

| "collection_binop_type SetMinusOp (Set \<tau>) (Set \<sigma>) (Set \<tau>)"
| "collection_binop_type SymmetricDifferenceOp (Set \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"

| "element_type \<tau> \<rho> \<Longrightarrow> update_element_type \<tau> (\<rho> \<squnion> \<sigma>) \<upsilon> \<Longrightarrow>
   collection_binop_type IncludingOp \<tau> \<sigma> \<upsilon>"
| "element_type \<tau> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow>
   collection_binop_type ExcludingOp \<tau> \<sigma> \<tau>"

| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type AppendOp (OrderedSet \<tau>) \<sigma> (OrderedSet \<tau>)"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type AppendOp (Sequence \<tau>) \<sigma> (Sequence \<tau>)"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type PrependOp (OrderedSet \<tau>) \<sigma> (OrderedSet \<tau>)"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type PrependOp (Sequence \<tau>) \<sigma> (Sequence \<tau>)"

| "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   collection_binop_type CollectionAtOp (OrderedSet \<tau>) \<sigma> \<tau>"
| "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   collection_binop_type CollectionAtOp (Sequence \<tau>) \<sigma> \<tau>"

| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type CollectionIndexOfOp (OrderedSet \<tau>) \<sigma> Integer[1]"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type CollectionIndexOfOp (Sequence \<tau>) \<sigma> Integer[1]"

inductive collection_ternop_type where
  "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow> \<rho> \<le> \<tau> \<Longrightarrow>
   collection_ternop_type InsertAtOp (OrderedSet \<tau>) \<sigma> \<rho> (OrderedSet \<tau>)"
| "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow> \<rho> \<le> \<tau> \<Longrightarrow>
   collection_ternop_type InsertAtOp (Sequence \<tau>) \<sigma> \<rho> (Sequence \<tau>)"
| "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   \<rho> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   collection_ternop_type SubOrderedSetOp (OrderedSet \<tau>) \<sigma> \<rho> (OrderedSet \<tau>)"
| "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   \<rho> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   collection_ternop_type SubSequenceOp (Sequence \<tau>) \<sigma> \<rho> (Sequence \<tau>)"

subsection \<open>Coercions\<close>

inductive unop_type where
  "any_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inl op) DotCall \<tau> \<sigma>"
| "boolean_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inr (Inl op)) DotCall \<tau> \<sigma>"
| "numeric_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inr (Inr (Inl op))) DotCall \<tau> \<sigma>"
| "string_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inr (Inr (Inr (Inl op)))) DotCall \<tau> \<sigma>"
| "collection_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inr (Inr (Inr (Inr op)))) ArrowCall \<tau> \<sigma>"

inductive binop_type where
  "super_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inl op) DotCall \<tau> \<sigma> \<rho>"
| "boolean_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inr (Inl op)) DotCall \<tau> \<sigma> \<rho>"
| "numeric_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inr (Inr (Inl op))) DotCall \<tau> \<sigma> \<rho>"
| "string_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inr (Inr (Inr (Inl op)))) DotCall \<tau> \<sigma> \<rho>"
| "collection_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inr (Inr (Inr (Inr op)))) ArrowCall \<tau> \<sigma> \<rho>"

inductive ternop_type where
  "string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon> \<Longrightarrow>
   ternop_type (Inl op) DotCall \<tau> \<sigma> \<rho> \<upsilon>"
| "collection_ternop_type op \<tau> \<sigma> \<rho> \<upsilon> \<Longrightarrow>
   ternop_type (Inr op) ArrowCall \<tau> \<sigma> \<rho> \<upsilon>"

inductive op_type where
  "unop_type op k \<tau> \<upsilon> \<Longrightarrow>
   op_type (Inl op) k \<tau> [] \<upsilon>"
| "binop_type op k \<tau> \<sigma> \<upsilon> \<Longrightarrow>
   op_type (Inr (Inl op)) k \<tau> [\<sigma>] \<upsilon>"
| "ternop_type op k \<tau> \<sigma> \<rho> \<upsilon> \<Longrightarrow>
   op_type (Inr (Inr (Inl op))) k \<tau> [\<sigma>, \<rho>] \<upsilon>"
| "operation \<tau> op \<pi> oper \<Longrightarrow>
   op_type (Inr (Inr (Inr op))) DotCall \<tau> \<pi> (oper_type oper)"

(*** Simplification Rules ***************************************************)

subsection \<open>Simplification Rules\<close>

inductive_simps op_type_alt_simps:
"mataop_type \<tau> op \<sigma>"
"typeop_type k op \<tau> \<sigma> \<rho>"

"op_type op k \<tau> \<pi> \<sigma>"
"unop_type op k \<tau> \<sigma>"
"binop_type op k \<tau> \<sigma> \<rho>"
"ternop_type op k \<tau> \<sigma> \<rho> \<upsilon>"

"any_unop_type op \<tau> \<sigma>"
"boolean_unop_type op \<tau> \<sigma>"
"numeric_unop_type op \<tau> \<sigma>"
"string_unop_type op \<tau> \<sigma>"
"collection_unop_type op \<tau> \<sigma>"

"super_binop_type op \<tau> \<sigma> \<rho>"
"boolean_binop_type op \<tau> \<sigma> \<rho>"
"numeric_binop_type op \<tau> \<sigma> \<rho>"
"string_binop_type op \<tau> \<sigma> \<rho>"
"collection_binop_type op \<tau> \<sigma> \<rho>"

"string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>"
"collection_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>"

(*** Determinism ************************************************************)

subsection \<open>Determinism\<close>

lemma typeop_type_det:
  "typeop_type op k \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   typeop_type op k \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: typeop_type.induct;
      auto simp add: typeop_type.simps update_element_type_det)

lemma any_unop_type_det:
  "any_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   any_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: any_unop_type.induct; simp add: any_unop_type.simps)

lemma boolean_unop_type_det:
  "boolean_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   boolean_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: boolean_unop_type.induct; simp add: boolean_unop_type.simps)

lemma numeric_unop_type_det:
  "numeric_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   numeric_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: numeric_unop_type.induct; auto simp add: numeric_unop_type.simps)

lemma string_unop_type_det:
  "string_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   string_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: string_unop_type.induct; simp add: string_unop_type.simps)

lemma collection_unop_type_det:
  "collection_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   collection_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  apply (induct rule: collection_unop_type.induct)
  by (erule collection_unop_type.cases;
      auto simp add: element_type_det update_element_type_det)+

lemma unop_type_det:
  "unop_type op k \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   unop_type op k \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: unop_type.induct;
      simp add: unop_type.simps any_unop_type_det
                boolean_unop_type_det numeric_unop_type_det
                string_unop_type_det collection_unop_type_det)

lemma super_binop_type_det:
  "super_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   super_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: super_binop_type.induct; auto simp add: super_binop_type.simps)

lemma boolean_binop_type_det:
  "boolean_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   boolean_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: boolean_binop_type.induct; simp add: boolean_binop_type.simps)

lemma numeric_binop_type_det:
  "numeric_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   numeric_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: numeric_binop_type.induct;
      auto simp add: numeric_binop_type.simps split: if_splits)

lemma string_binop_type_det:
  "string_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   string_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: string_binop_type.induct; simp add: string_binop_type.simps)

lemma collection_binop_type_det:
  "collection_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   collection_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  apply (induct rule: collection_binop_type.induct; simp add: collection_binop_type.simps)
  using element_type_det update_element_type_det by blast+

lemma binop_type_det:
  "binop_type op k \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   binop_type op k \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: binop_type.induct;
      simp add: binop_type.simps super_binop_type_det
                boolean_binop_type_det numeric_binop_type_det
                string_binop_type_det collection_binop_type_det)

lemma string_ternop_type_det:
  "string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>1 \<Longrightarrow>
   string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>2 \<Longrightarrow> \<upsilon>\<^sub>1 = \<upsilon>\<^sub>2"
  by (induct rule: string_ternop_type.induct; simp add: string_ternop_type.simps)

lemma collection_ternop_type_det:
  "collection_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>1 \<Longrightarrow>
   collection_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>2 \<Longrightarrow> \<upsilon>\<^sub>1 = \<upsilon>\<^sub>2"
  by (induct rule: collection_ternop_type.induct; simp add: collection_ternop_type.simps)

lemma ternop_type_det:
  "ternop_type op k \<tau> \<sigma> \<rho> \<upsilon>\<^sub>1 \<Longrightarrow>
   ternop_type op k \<tau> \<sigma> \<rho> \<upsilon>\<^sub>2 \<Longrightarrow> \<upsilon>\<^sub>1 = \<upsilon>\<^sub>2"
  by (induct rule: ternop_type.induct;
      simp add: ternop_type.simps string_ternop_type_det collection_ternop_type_det)

lemma op_type_det:
  "op_type op k \<tau> \<pi> \<sigma> \<Longrightarrow>
   op_type op k \<tau> \<pi> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  apply (induct rule: op_type.induct)
  apply (erule op_type.cases; simp add: unop_type_det)
  apply (erule op_type.cases; simp add: binop_type_det)
  apply (erule op_type.cases; simp add: ternop_type_det)
  by (erule op_type.cases; simp; metis operation_det)

(*** Expressions Typing *****************************************************)

section \<open>Expressions Typing\<close>

text \<open>
  The following typing rules are preliminary. The final rules are given at
  the end of the next chapter.\<close>

inductive typing :: "('a :: ocl_object_model) type env \<Rightarrow> 'a expr \<Rightarrow> 'a type \<Rightarrow> bool"
       ("(1_/ \<turnstile>\<^sub>E/ (_ :/ _))" [51,51,51] 50)
    and collection_parts_typing ("(1_/ \<turnstile>\<^sub>C/ (_ :/ _))" [51,51,51] 50)
    and collection_part_typing ("(1_/ \<turnstile>\<^sub>P/ (_ :/ _))" [51,51,51] 50)
    and iterator_typing ("(1_/ \<turnstile>\<^sub>I/ (_ :/ _))" [51,51,51] 50)
    and expr_list_typing ("(1_/ \<turnstile>\<^sub>L/ (_ :/ _))" [51,51,51] 50) where

\<comment> \<open>Primitive Literals\<close>

 NullLiteralT:
  "\<Gamma> \<turnstile>\<^sub>E NullLiteral : OclVoid[?]"
|BooleanLiteralT:
  "\<Gamma> \<turnstile>\<^sub>E BooleanLiteral c : Boolean[1]"
|RealLiteralT:
  "\<Gamma> \<turnstile>\<^sub>E RealLiteral c : Real[1]"
|IntegerLiteralT:
  "\<Gamma> \<turnstile>\<^sub>E IntegerLiteral c : Integer[1]"
|UnlimitedNaturalLiteralT:
  "\<Gamma> \<turnstile>\<^sub>E UnlimitedNaturalLiteral c : UnlimitedNatural[1]"
|StringLiteralT:
  "\<Gamma> \<turnstile>\<^sub>E StringLiteral c : String[1]"
|EnumLiteralT:
  "has_literal enum lit \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E EnumLiteral enum lit : (Enum enum)[1]"

\<comment> \<open>Collection Literals\<close>

|SetLiteralT:
  "\<Gamma> \<turnstile>\<^sub>C prts : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectionLiteral SetKind prts : Set \<tau>"
|OrderedSetLiteralT:
  "\<Gamma> \<turnstile>\<^sub>C prts : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectionLiteral OrderedSetKind prts : OrderedSet \<tau>"
|BagLiteralT:
  "\<Gamma> \<turnstile>\<^sub>C prts : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectionLiteral BagKind prts : Bag \<tau>"
|SequenceLiteralT:
  "\<Gamma> \<turnstile>\<^sub>C prts : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectionLiteral SequenceKind prts : Sequence \<tau>"

\<comment> \<open>We prohibit empty collection literals, because their type is unclear.
  We could use @{text "OclVoid[1]"} element type for empty collections, but
  the typing rules will give wrong types for nested collections, because,
  for example, @{text "OclVoid[1] \<squnion> Set(Integer[1]) = OclSuper"}\<close>

|CollectionPartsSingletonT:
  "\<Gamma> \<turnstile>\<^sub>P x : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>C [x] : \<tau>"
|CollectionPartsListT:
  "\<Gamma> \<turnstile>\<^sub>P x : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>C y # xs : \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>C x # y # xs : \<tau> \<squnion> \<sigma>"

|CollectionPartItemT:
  "\<Gamma> \<turnstile>\<^sub>E a : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>P CollectionItem a : \<tau>"
|CollectionPartRangeT:
  "\<Gamma> \<turnstile>\<^sub>E a : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E b : \<sigma> \<Longrightarrow>
   \<tau> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   \<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>P CollectionRange a b : Integer[1]"

\<comment> \<open>Tuple Literals\<close>
\<comment> \<open>We do not prohibit empty tuples, because it could be useful.
  @{text "Tuple()"} is a supertype of all other tuple types.\<close>

|TupleLiteralNilT:
  "\<Gamma> \<turnstile>\<^sub>E TupleLiteral [] : Tuple fmempty"
|TupleLiteralConsT:
  "\<Gamma> \<turnstile>\<^sub>E TupleLiteral elems : Tuple \<xi> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E tuple_element_expr el : \<tau> \<Longrightarrow>
   tuple_element_type el = Some \<sigma> \<Longrightarrow>
   \<tau> \<le> \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E TupleLiteral (el # elems) : Tuple (\<xi>(tuple_element_name el \<mapsto>\<^sub>f \<sigma>))"

\<comment> \<open>Misc Expressions\<close>

|LetT:
  "\<Gamma> \<turnstile>\<^sub>E init : \<sigma> \<Longrightarrow>
   \<sigma> \<le> \<tau> \<Longrightarrow>
   \<Gamma>(v \<mapsto>\<^sub>f \<tau>) \<turnstile>\<^sub>E body : \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E Let v (Some \<tau>) init body : \<rho>"
|VarT:
  "fmlookup \<Gamma> v = Some \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E Var v : \<tau>"
|IfT:
  "\<Gamma> \<turnstile>\<^sub>E a : Boolean[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E b : \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E c : \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E If a b c : \<sigma> \<squnion> \<rho>"

\<comment> \<open>Call Expressions\<close>

|MetaOperationCallT:
  "mataop_type \<tau> op \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E MetaOperationCall \<tau> op : \<sigma>"
|StaticOperationCallT:
  "\<Gamma> \<turnstile>\<^sub>L params : \<pi> \<Longrightarrow>
   static_operation \<tau> op \<pi> oper \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E StaticOperationCall \<tau> op params : oper_type oper"

|TypeOperationCallT:
  "\<Gamma> \<turnstile>\<^sub>E a : \<tau> \<Longrightarrow>
   typeop_type k op \<tau> \<sigma> \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E TypeOperationCall a k op \<sigma> : \<rho>"

|AttributeCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<C>\<rangle>\<^sub>\<T>[1] \<Longrightarrow>
   attribute \<C> prop \<D> \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AttributeCall src DotCall prop : \<tau>"
|AssociationEndCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<C>\<rangle>\<^sub>\<T>[1] \<Longrightarrow>
   association_end \<C> from role \<D> end \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AssociationEndCall src DotCall from role : assoc_end_type end"
|AssociationClassCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<C>\<rangle>\<^sub>\<T>[1] \<Longrightarrow>
   referred_by_association_class \<C> from \<A> \<D> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AssociationClassCall src DotCall from \<A> : class_assoc_type \<A>"
|AssociationClassEndCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<A>\<rangle>\<^sub>\<T>[1] \<Longrightarrow>
   association_class_end \<A> role end \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AssociationClassEndCall src DotCall role : class_assoc_end_type end"
|OperationCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L params : \<pi> \<Longrightarrow>
   op_type op k \<tau> \<pi> \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E OperationCall src k op params : \<sigma>"

|TupleElementCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : Tuple \<pi> \<Longrightarrow>
   fmlookup \<pi> elem = Some \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E TupleElementCall src DotCall elem : \<tau>"

\<comment> \<open>Iterator Expressions\<close>

|IteratorT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<tau> \<Longrightarrow>
   element_type \<tau> \<sigma> \<Longrightarrow>
   \<sigma> \<le> its_ty \<Longrightarrow>
   \<Gamma> ++\<^sub>f fmap_of_list (map (\<lambda>it. (it, its_ty)) its) \<turnstile>\<^sub>E body : \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>I (src, its, (Some its_ty), body) : (\<tau>, \<sigma>, \<rho>)"

|IterateT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, Let res (Some res_t) res_init body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   \<rho> \<le> res_t \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E IterateCall src ArrowCall its its_ty res (Some res_t) res_init body : \<rho>"

|AnyIteratorT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AnyIteratorCall src ArrowCall its its_ty body : \<sigma>"
|ClosureIteratorT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_single_type \<rho> \<le> \<sigma> \<Longrightarrow>
   to_unique_collection \<tau> \<upsilon> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E ClosureIteratorCall src ArrowCall its its_ty body : \<upsilon>"
|CollectIteratorT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_nonunique_collection \<tau> \<upsilon> \<Longrightarrow>
   update_element_type \<upsilon> (to_single_type \<rho>) \<phi> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectIteratorCall src ArrowCall its its_ty body : \<phi>"
|CollectNestedIteratorT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_nonunique_collection \<tau> \<upsilon> \<Longrightarrow>
   update_element_type \<upsilon> \<rho> \<phi> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectNestedIteratorCall src ArrowCall its its_ty body : \<phi>"
|ExistsIteratorT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E ExistsIteratorCall src ArrowCall its its_ty body : \<rho>"
|ForAllIteratorT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E ForAllIteratorCall src ArrowCall its its_ty body : \<rho>"
|OneIteratorT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E OneIteratorCall src ArrowCall its its_ty body : Boolean[1]"
|IsUniqueIteratorT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E IsUniqueIteratorCall src ArrowCall its its_ty body : Boolean[1]"
|SelectIteratorT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E SelectIteratorCall src ArrowCall its its_ty body : \<tau>"
|RejectIteratorT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E RejectIteratorCall src ArrowCall its its_ty body : \<tau>"
|SortedByIteratorT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_ordered_collection \<tau> \<upsilon> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E SortedByIteratorCall src ArrowCall its its_ty body : \<upsilon>"

\<comment> \<open>Expression Lists\<close>

|ExprListNilT:
  "\<Gamma> \<turnstile>\<^sub>L [] : []"
|ExprListConsT:
  "\<Gamma> \<turnstile>\<^sub>E expr : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L exprs : \<pi> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L expr # exprs : \<tau> # \<pi>"

(*** Elimination Rules ******************************************************)

section \<open>Elimination Rules\<close>

inductive_cases NullLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E NullLiteral : \<tau>"
inductive_cases BooleanLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E BooleanLiteral c : \<tau>"
inductive_cases RealLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E RealLiteral c : \<tau>"
inductive_cases IntegerLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E IntegerLiteral c : \<tau>"
inductive_cases UnlimitedNaturalLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E UnlimitedNaturalLiteral c : \<tau>"
inductive_cases StringLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E StringLiteral c : \<tau>"
inductive_cases EnumLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E EnumLiteral enm lit : \<tau>"
inductive_cases CollectionLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E CollectionLiteral k prts : \<tau>"
inductive_cases TupleLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E TupleLiteral elems : \<tau>"

inductive_cases LetTE [elim]: "\<Gamma> \<turnstile>\<^sub>E Let v \<tau> init body : \<sigma>"
inductive_cases VarTE [elim]: "\<Gamma> \<turnstile>\<^sub>E Var v : \<tau>"
inductive_cases IfTE [elim]: "\<Gamma> \<turnstile>\<^sub>E If a b c : \<tau>"

inductive_cases MetaOperationCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E MetaOperationCall \<tau> op : \<sigma>"
inductive_cases StaticOperationCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E StaticOperationCall \<tau> op as : \<sigma>"

inductive_cases TypeOperationCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E TypeOperationCall a k op \<sigma> : \<tau>"
inductive_cases AttributeCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AttributeCall src k prop : \<tau>"
inductive_cases AssociationEndCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AssociationEndCall src k role from : \<tau>"
inductive_cases AssociationClassCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AssociationClassCall src k a from : \<tau>"
inductive_cases AssociationClassEndCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AssociationClassEndCall src k role : \<tau>"
inductive_cases OperationCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E OperationCall src k op params : \<tau>"
inductive_cases TupleElementCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E TupleElementCall src k elem : \<tau>"

inductive_cases IteratorTE [elim]: "\<Gamma> \<turnstile>\<^sub>I (src, its, body) : ys"
inductive_cases IterateTE [elim]: "\<Gamma> \<turnstile>\<^sub>E IterateCall src k its its_ty res res_t res_init body : \<tau>"
inductive_cases AnyIteratorTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AnyIteratorCall src k its its_ty body : \<tau>"
inductive_cases ClosureIteratorTE [elim]: "\<Gamma> \<turnstile>\<^sub>E ClosureIteratorCall src k its its_ty body : \<tau>"
inductive_cases CollectIteratorTE [elim]: "\<Gamma> \<turnstile>\<^sub>E CollectIteratorCall src k its its_ty body : \<tau>"
inductive_cases CollectNestedIteratorTE [elim]: "\<Gamma> \<turnstile>\<^sub>E CollectNestedIteratorCall src k its its_ty body : \<tau>"
inductive_cases ExistsIteratorTE [elim]: "\<Gamma> \<turnstile>\<^sub>E ExistsIteratorCall src k its its_ty body : \<tau>"
inductive_cases ForAllIteratorTE [elim]: "\<Gamma> \<turnstile>\<^sub>E ForAllIteratorCall src k its its_ty body : \<tau>"
inductive_cases OneIteratorTE [elim]: "\<Gamma> \<turnstile>\<^sub>E OneIteratorCall src k its its_ty body : \<tau>"
inductive_cases IsUniqueIteratorTE [elim]: "\<Gamma> \<turnstile>\<^sub>E IsUniqueIteratorCall src k its its_ty body : \<tau>"
inductive_cases SelectIteratorTE [elim]: "\<Gamma> \<turnstile>\<^sub>E SelectIteratorCall src k its its_ty body : \<tau>"
inductive_cases RejectIteratorTE [elim]: "\<Gamma> \<turnstile>\<^sub>E RejectIteratorCall src k its its_ty body : \<tau>"
inductive_cases SortedByIteratorTE [elim]: "\<Gamma> \<turnstile>\<^sub>E SortedByIteratorCall src k its its_ty body : \<tau>"

inductive_cases CollectionPartsNilTE [elim]: "\<Gamma> \<turnstile>\<^sub>C [x] : \<tau>"
inductive_cases CollectionPartsItemTE [elim]: "\<Gamma> \<turnstile>\<^sub>C x # y # xs : \<tau>"

inductive_cases CollectionItemTE [elim]: "\<Gamma> \<turnstile>\<^sub>P CollectionItem a : \<tau>"
inductive_cases CollectionRangeTE [elim]: "\<Gamma> \<turnstile>\<^sub>P CollectionRange a b : \<tau>"

inductive_cases ExprListTE [elim]: "\<Gamma> \<turnstile>\<^sub>L exprs : \<pi>"

(*** Simplification Rules ***************************************************)

section \<open>Simplification Rules\<close>

inductive_simps typing_alt_simps: 
"\<Gamma> \<turnstile>\<^sub>E NullLiteral : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E BooleanLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E RealLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E UnlimitedNaturalLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E IntegerLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E StringLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E EnumLiteral enm lit : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectionLiteral k prts : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E TupleLiteral [] : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E TupleLiteral (x # xs) : \<tau>"

"\<Gamma> \<turnstile>\<^sub>E Let v \<tau> init body : \<sigma>"
"\<Gamma> \<turnstile>\<^sub>E Var v : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E If a b c : \<tau>"

"\<Gamma> \<turnstile>\<^sub>E MetaOperationCall \<tau> op : \<sigma>"
"\<Gamma> \<turnstile>\<^sub>E StaticOperationCall \<tau> op as : \<sigma>"

"\<Gamma> \<turnstile>\<^sub>E TypeOperationCall a k op \<sigma> : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AttributeCall src k prop : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AssociationEndCall src k role from : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AssociationClassCall src k a from : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AssociationClassEndCall src k role : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E OperationCall src k op params : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E TupleElementCall src k elem : \<tau>"

"\<Gamma> \<turnstile>\<^sub>I (src, its, body) : ys"
"\<Gamma> \<turnstile>\<^sub>E IterateCall src k its its_ty res res_t res_init body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AnyIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E ClosureIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectNestedIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E ExistsIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E ForAllIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E OneIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E IsUniqueIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E SelectIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E RejectIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E SortedByIteratorCall src k its its_ty body : \<tau>"

"\<Gamma> \<turnstile>\<^sub>C [x] : \<tau>"
"\<Gamma> \<turnstile>\<^sub>C x # y # xs : \<tau>"

"\<Gamma> \<turnstile>\<^sub>P CollectionItem a : \<tau>"
"\<Gamma> \<turnstile>\<^sub>P CollectionRange a b : \<tau>"

"\<Gamma> \<turnstile>\<^sub>L [] : \<pi>"
"\<Gamma> \<turnstile>\<^sub>L x # xs : \<pi>"

(*** Determinism ************************************************************)

section \<open>Determinism\<close>

lemma
  typing_det:
    "\<Gamma> \<turnstile>\<^sub>E expr : \<tau> \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>E expr : \<sigma> \<Longrightarrow> \<tau> = \<sigma>" and
  collection_parts_typing_det:
    "\<Gamma> \<turnstile>\<^sub>C prts : \<tau> \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>C prts : \<sigma> \<Longrightarrow> \<tau> = \<sigma>" and
  collection_part_typing_det:
    "\<Gamma> \<turnstile>\<^sub>P prt : \<tau> \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>P prt : \<sigma> \<Longrightarrow> \<tau> = \<sigma>" and
  iterator_typing_det:
    "\<Gamma> \<turnstile>\<^sub>I (src, its, body) : xs \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>I (src, its, body) : ys \<Longrightarrow> xs = ys" and
  expr_list_typing_det:
    "\<Gamma> \<turnstile>\<^sub>L exprs : \<pi> \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>L exprs : \<xi> \<Longrightarrow> \<pi> = \<xi>"
proof (induct arbitrary: \<sigma> and \<sigma> and \<sigma> and ys and \<xi>
       rule: typing_collection_parts_typing_collection_part_typing_iterator_typing_expr_list_typing.inducts)
  case (NullLiteralT \<Gamma>) thus ?case by auto
next
  case (BooleanLiteralT \<Gamma> c) thus ?case by auto
next
  case (RealLiteralT \<Gamma> c) thus ?case by auto
next
  case (IntegerLiteralT \<Gamma> c) thus ?case by auto
next
  case (UnlimitedNaturalLiteralT \<Gamma> c) thus ?case by auto
next
  case (StringLiteralT \<Gamma> c) thus ?case by auto
next
  case (EnumLiteralT \<Gamma> \<tau> lit) thus ?case by auto
next
  case (SetLiteralT \<Gamma> prts \<tau>) thus ?case by blast
next
  case (OrderedSetLiteralT \<Gamma> prts \<tau>) thus ?case by blast
next
  case (BagLiteralT \<Gamma> prts \<tau>) thus ?case by blast
next
  case (SequenceLiteralT \<Gamma> prts \<tau>) thus ?case by blast
next
  case (CollectionPartsSingletonT \<Gamma> x \<tau>) thus ?case by blast
next
  case (CollectionPartsListT \<Gamma> x \<tau> y xs \<sigma>) thus ?case by blast
next
  case (CollectionPartItemT \<Gamma> a \<tau>) thus ?case by blast
next
  case (CollectionPartRangeT \<Gamma> a \<tau> b \<sigma>) thus ?case by blast
next
  case (TupleLiteralNilT \<Gamma>) thus ?case by auto
next
  case (TupleLiteralConsT \<Gamma> elems \<xi> el \<tau>) show ?case
    apply (insert TupleLiteralConsT.prems)
    apply (erule TupleLiteralTE, simp)
    using TupleLiteralConsT.hyps by auto
next
  case (LetT \<Gamma> \<M> init \<sigma> \<tau> v body \<rho>) thus ?case by blast
next
  case (VarT \<Gamma> v \<tau> \<M>) thus ?case by auto
next
  case (IfT \<Gamma> a \<tau> b \<sigma> c \<rho>) thus ?case
    apply (insert IfT.prems)
    apply (erule IfTE)
    by (simp add: IfT.hyps)
next
  case (MetaOperationCallT \<tau> op \<sigma> \<Gamma>) thus ?case
    by (metis MetaOperationCallTE mataop_type.cases)
next
  case (StaticOperationCallT \<tau> op \<pi> oper \<Gamma> as) thus ?case
    apply (insert StaticOperationCallT.prems)
    apply (erule StaticOperationCallTE)
    using StaticOperationCallT.hyps static_operation_det by blast
next
  case (TypeOperationCallT \<Gamma> a \<tau> op \<sigma> \<rho>) thus ?case
    by (metis TypeOperationCallTE typeop_type_det)
next
  case (AttributeCallT \<Gamma> src \<tau> \<C> "prop" \<D> \<sigma>) show ?case
    apply (insert AttributeCallT.prems)
    apply (erule AttributeCallTE)
    using AttributeCallT.hyps attribute_det by blast
next
  case (AssociationEndCallT \<Gamma> src \<C> "from" role \<D> "end") show ?case
    apply (insert AssociationEndCallT.prems)
    apply (erule AssociationEndCallTE)
    using AssociationEndCallT.hyps association_end_det by blast
next
  case (AssociationClassCallT \<Gamma> src \<C> "from" \<A>) thus ?case by blast
next
  case (AssociationClassEndCallT \<Gamma> src \<tau> \<A> role "end") show ?case
    apply (insert AssociationClassEndCallT.prems)
    apply (erule AssociationClassEndCallTE)
    using AssociationClassEndCallT.hyps association_class_end_det by blast
next
  case (OperationCallT \<Gamma> src \<tau> params \<pi> op k) show ?case
    apply (insert OperationCallT.prems)
    apply (erule OperationCallTE)
    using OperationCallT.hyps op_type_det by blast
next
  case (TupleElementCallT \<Gamma> src \<pi> elem \<tau>) thus ?case 
    apply (insert TupleElementCallT.prems)
    apply (erule TupleElementCallTE)
    using TupleElementCallT.hyps by fastforce
next
  case (IteratorT \<Gamma> src \<tau> \<sigma> its_ty its body \<rho>) show ?case
    apply (insert IteratorT.prems)
    apply (erule IteratorTE)
    using IteratorT.hyps element_type_det by blast
next
  case (IterateT \<Gamma> src its its_ty res res_t res_init body \<tau> \<sigma> \<rho>) show ?case
    apply (insert IterateT.prems)
    using IterateT.hyps by blast
next
  case (AnyIteratorT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho>) thus ?case
    by (meson AnyIteratorTE Pair_inject)
next
  case (ClosureIteratorT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> \<upsilon>) show ?case
    apply (insert ClosureIteratorT.prems)
    apply (erule ClosureIteratorTE)
    using ClosureIteratorT.hyps to_unique_collection_det by blast
next
  case (CollectIteratorT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> \<upsilon>) show ?case
    apply (insert CollectIteratorT.prems)
    apply (erule CollectIteratorTE)
    using CollectIteratorT.hyps to_nonunique_collection_det
      update_element_type_det Pair_inject by metis
next
  case (CollectNestedIteratorT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> \<upsilon>) show ?case
    apply (insert CollectNestedIteratorT.prems)
    apply (erule CollectNestedIteratorTE)
    using CollectNestedIteratorT.hyps to_nonunique_collection_det
      update_element_type_det Pair_inject by metis
next
  case (ExistsIteratorT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho>) show ?case
    apply (insert ExistsIteratorT.prems)
    apply (erule ExistsIteratorTE)
    using ExistsIteratorT.hyps Pair_inject by metis
next
  case (ForAllIteratorT \<Gamma> \<M> src its its_ty body \<tau> \<sigma> \<rho>) show ?case
    apply (insert ForAllIteratorT.prems)
    apply (erule ForAllIteratorTE)
    using ForAllIteratorT.hyps Pair_inject by metis
next
  case (OneIteratorT \<Gamma> \<M> src its its_ty body \<tau> \<sigma> \<rho>) show ?case
    apply (insert OneIteratorT.prems)
    apply (erule OneIteratorTE)
    by simp
next
  case (IsUniqueIteratorT \<Gamma> \<M> src its its_ty body \<tau> \<sigma> \<rho>) show ?case
    apply (insert IsUniqueIteratorT.prems)
    apply (erule IsUniqueIteratorTE)
    by simp
next
  case (SelectIteratorT \<Gamma> \<M> src its its_ty body \<tau> \<sigma> \<rho>) show ?case
    apply (insert SelectIteratorT.prems)
    apply (erule SelectIteratorTE)
    using SelectIteratorT.hyps by blast
next
  case (RejectIteratorT \<Gamma> \<M> src its its_ty body \<tau> \<sigma> \<rho>) show ?case
    apply (insert RejectIteratorT.prems)
    apply (erule RejectIteratorTE)
    using RejectIteratorT.hyps by blast
next
  case (SortedByIteratorT \<Gamma> \<M> src its its_ty body \<tau> \<sigma> \<rho> \<upsilon>) show ?case
    apply (insert SortedByIteratorT.prems)
    apply (erule SortedByIteratorTE)
    using SortedByIteratorT.hyps to_ordered_collection_det by blast
next
  case (ExprListNilT \<Gamma>) thus ?case
    using expr_list_typing.cases by auto
next
  case (ExprListConsT \<Gamma> expr \<tau> exprs \<pi>) show ?case
    apply (insert ExprListConsT.prems)
    apply (erule ExprListTE)
    by (simp_all add: ExprListConsT.hyps)
qed

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred op_type .
code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) iterator_typing .

end
