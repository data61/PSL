(*  Title:      HOL/MicroJava/J/Decl.thy

    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

section \<open>Class Declarations and Programs\<close>

theory Decl imports Type begin

type_synonym 
  fdecl    = "vname \<times> ty"        \<comment> \<open>field declaration\<close>
type_synonym
  'm mdecl = "mname \<times> ty list \<times> ty \<times> 'm"     \<comment> \<open>method = name, arg.\ types, return type, body\<close>
type_synonym
  'm "class" = "cname \<times> fdecl list \<times> 'm mdecl list"       \<comment> \<open>class = superclass, fields, methods\<close>
type_synonym
  'm cdecl = "cname \<times> 'm class"  \<comment> \<open>class declaration\<close>
type_synonym
  'm prog  = "'m cdecl list"     \<comment> \<open>program\<close>

(*<*)
translations
  (type) "fdecl"   <= (type) "vname \<times> ty"
  (type) "'c mdecl" <= (type) "mname \<times> ty list \<times> ty \<times> 'c"
  (type) "'c class" <= (type) "cname \<times> fdecl list \<times> ('c mdecl) list"
  (type) "'c cdecl" <= (type) "cname \<times> ('c class)"
  (type) "'c prog" <= (type) "('c cdecl) list"
(*>*)

definition "class" :: "'m prog \<Rightarrow> cname \<rightharpoonup> 'm class"
where
  "class  \<equiv>  map_of"

definition is_class :: "'m prog \<Rightarrow> cname \<Rightarrow> bool"
where
  "is_class P C  \<equiv>  class P C \<noteq> None"

lemma finite_is_class: "finite {C. is_class P C}"

(*<*)
apply (unfold is_class_def class_def)
apply (fold dom_def)
apply (rule finite_dom_map_of)
done
(*>*)

definition is_type :: "'m prog \<Rightarrow> ty \<Rightarrow> bool"
where
  "is_type P T  \<equiv>
  (case T of Void \<Rightarrow> True | Boolean \<Rightarrow> True | Integer \<Rightarrow> True | NT \<Rightarrow> True
   | Class C \<Rightarrow> is_class P C)"

lemma is_type_simps [simp]:
  "is_type P Void \<and> is_type P Boolean \<and> is_type P Integer \<and>
  is_type P NT \<and> is_type P (Class C) = is_class P C"
(*<*)by(simp add:is_type_def)(*>*)


abbreviation
  "types P == Collect (is_type P)"

end
