(*  Title:      JinjaThreads/Common/Decl.thy
    Author:     David von Oheimb, Andreas Lochbihler

    Based on the Jinja theory Common/Decl.thy by David von Oheimb
*)

section \<open>Class Declarations and Programs\<close>

theory Decl
imports
  Type
begin

type_synonym volatile = bool

record fmod =
  volatile :: volatile

type_synonym fdecl    = "vname \<times> ty \<times> fmod"        \<comment> \<open>field declaration\<close>
type_synonym 'm mdecl = "mname \<times> ty list \<times> ty \<times> 'm"     \<comment> \<open>method = name, arg. types, return type, body\<close>
type_synonym 'm mdecl' = "mname \<times> ty list \<times> ty \<times> 'm option"     \<comment> \<open>method = name, arg. types, return type, possible body\<close>
type_synonym 'm "class" = "cname \<times> fdecl list \<times> 'm mdecl' list"       \<comment> \<open>class = superclass, fields, methods\<close>
type_synonym 'm cdecl = "cname \<times> 'm class"  \<comment> \<open>class declaration\<close>

datatype
  'm prog = Program "'m cdecl list" 

translations
  (type) "fdecl"   <= (type) "String.literal \<times> ty \<times> fmod"
  (type) "'c mdecl" <= (type) "String.literal \<times> ty list \<times> ty \<times> 'c"
  (type) "'c mdecl'" <= (type) "String.literal \<times> ty list \<times> ty \<times> 'c option"
  (type) "'c class" <= (type) "String.literal \<times> fdecl list \<times> ('c mdecl) list"
  (type) "'c cdecl" <= (type) "String.literal \<times> ('c class)"

notation (input) None ("Native")

primrec "classes" :: "'m prog \<Rightarrow> 'm cdecl list"
where
  "classes (Program P) = P"

primrec "class" :: "'m prog \<Rightarrow> cname \<rightharpoonup> 'm class"
where
  "class (Program p) = map_of p"

locale prog =
  fixes P :: "'m prog"

definition is_class :: "'m prog \<Rightarrow> cname \<Rightarrow> bool"
where
  "is_class P C  \<equiv>  class P C \<noteq> None"

lemma finite_is_class: "finite {C. is_class P C}"
(*<*)
apply(cases P)
apply (unfold is_class_def)
apply (fold dom_def)
apply(simp add: finite_dom_map_of)
done
(*>*)

primrec is_type :: "'m prog \<Rightarrow> ty \<Rightarrow> bool"
where
  is_type_void:   "is_type P Void = True"
| is_type_bool:   "is_type P Boolean = True"
| is_type_int:    "is_type P Integer = True"
| is_type_nt:     "is_type P NT = True"
| is_type_class:  "is_type P (Class C) = is_class P C"
| is_type_array:  "is_type P (A\<lfloor>\<rceil>) = (case ground_type A of NT \<Rightarrow> False | Class C \<Rightarrow> is_class P C | _ \<Rightarrow> True)"

lemma is_type_ArrayD: "is_type P (T\<lfloor>\<rceil>) \<Longrightarrow> is_type P T"
by(induct T) auto

lemma is_type_ground_type:
  "is_type P T \<Longrightarrow> is_type P (ground_type T)"
by(induct T)(auto, metis is_type_ArrayD is_type_array)

abbreviation "types" :: "'m prog \<Rightarrow> ty set"
where "types P \<equiv> {T. is_type P T}"

abbreviation is_htype :: "'m prog \<Rightarrow> htype \<Rightarrow> bool"
where "is_htype P hT \<equiv> is_type P (ty_of_htype hT)"

subsection \<open>Code generation\<close>

lemma is_class_intros [code_pred_intro]:
  "class P C \<noteq> None \<Longrightarrow> is_class P C"
by(auto simp add: is_class_def)

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> bool)
  is_class 
unfolding is_class_def by simp

declare is_class_def[code]

end
