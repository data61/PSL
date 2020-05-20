section \<open>Usage\<close>

theory Test_Constructor_Funs
imports Constructor_Funs
begin

text \<open>
  This entry provides a @{command datatype} plugin and a separate command.
  The plugin runs by default on all defined datatypes, but it can be disabled individually:
\<close>

datatype (plugins del: "constructor_funs") 'a tree = Node | Fork 'a "'a tree list"

context begin

text \<open>
  The @{command constructor_funs} command can be used to add constructor functions if the plugin has
  been disabled during datatype definition.
\<close>

constructor_funs tree

end

text \<open>Records are supported.\<close>

record 'a meep =
  field1 :: 'a
  field2 :: nat

text \<open>Nested and mutual recursion are supported.\<close>

datatype
  'a mlist1 = MNil1 | MCons1 'a "'a mlist2" and
  'a mlist2 = MNil2 | MCons2 'a "'a mlist1"

section \<open>Examples\<close>

datatype 'a seq = Nil | Cons 'a "'a seq"

fun app :: "'a seq \<Rightarrow> 'a seq \<Rightarrow> 'a seq" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun map where
"map _ Nil = Nil" |
"map f (Cons x xs) = Cons (f x) (map f xs)"

definition "bla = map (Cons True) Nil"

text \<open>
  The generated code never calls constructors directly, but only through regular functions. These
  functions are defined in eta-long form.
\<close>

declare [["constructor_funs"]]

export_code app bla plus_nat_inst.plus_nat in SML

export_code app bla plus_nat_inst.plus_nat checking SML Scala

end
