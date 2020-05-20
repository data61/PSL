theory Design_generated_generated imports "../Toy_Library"   "../Toy_Library_Static" begin

(* 1 ************************************ 0 + 1 *)
text \<open>
  For certain concepts like classes and class-types, only a generic
  definition for its resulting semantics can be given. Generic means,
  there is a function outside HOL that ``compiles'' a concrete,
  closed-world class diagram into a ``theory'' of this data model,
  consisting of a bunch of definitions for classes, accessors, method,
  casts, and tests for actual types, as well as proofs for the
  fundamental properties of these operations in this concrete data
  model. \<close>

(* 2 ************************************ 1 + 1 *)
text \<open>
   Our data universe  consists in the concrete class diagram just of node's,
and implicitly of the class object. Each class implies the existence of a class
type defined for the corresponding object representations as follows: \<close>

(* 3 ************************************ 2 + 10 *)
datatype ty\<E>\<X>\<T>\<^sub>A\<^sub>t\<^sub>o\<^sub>m = mk\<E>\<X>\<T>\<^sub>A\<^sub>t\<^sub>o\<^sub>m "oid" "oid list option" "int option" "bool option" "nat option" "unit option"
datatype ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m = mk\<^sub>A\<^sub>t\<^sub>o\<^sub>m "ty\<E>\<X>\<T>\<^sub>A\<^sub>t\<^sub>o\<^sub>m" "int option"
datatype ty\<E>\<X>\<T>\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e = mk\<E>\<X>\<T>\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e_\<^sub>A\<^sub>t\<^sub>o\<^sub>m "ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m"
                        | mk\<E>\<X>\<T>\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e "oid" "oid list option" "int option" "bool option" "nat option" "unit option"
datatype ty\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e = mk\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e "ty\<E>\<X>\<T>\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e"
datatype ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e "ty\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e"
                        | mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<^sub>A\<^sub>t\<^sub>o\<^sub>m "ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m"
                        | mk\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "oid" "nat option" "unit option"
datatype ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty\<E>\<X>\<T>\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" "oid list option" "int option" "bool option"
datatype ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
                        | mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e "ty\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e"
                        | mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y_\<^sub>A\<^sub>t\<^sub>o\<^sub>m "ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m"
                        | mk\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "oid"
datatype ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y = mk\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "ty\<E>\<X>\<T>\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y" "nat option" "unit option"
datatype ty\<E>\<X>\<T>\<^sub>T\<^sub>o\<^sub>y\<^sub>A\<^sub>n\<^sub>y = mk\<E>\<X>\<T>\<^sub>T\<^sub>o\<^sub>y\<^sub>A\<^sub>n\<^sub>y_\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y"
                        | mk\<E>\<X>\<T>\<^sub>T\<^sub>o\<^sub>y\<^sub>A\<^sub>n\<^sub>y_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
                        | mk\<E>\<X>\<T>\<^sub>T\<^sub>o\<^sub>y\<^sub>A\<^sub>n\<^sub>y_\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e "ty\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e"
                        | mk\<E>\<X>\<T>\<^sub>T\<^sub>o\<^sub>y\<^sub>A\<^sub>n\<^sub>y_\<^sub>A\<^sub>t\<^sub>o\<^sub>m "ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m"
                        | mk\<E>\<X>\<T>\<^sub>T\<^sub>o\<^sub>y\<^sub>A\<^sub>n\<^sub>y "oid"
datatype ty\<^sub>T\<^sub>o\<^sub>y\<^sub>A\<^sub>n\<^sub>y = mk\<^sub>T\<^sub>o\<^sub>y\<^sub>A\<^sub>n\<^sub>y "ty\<E>\<X>\<T>\<^sub>T\<^sub>o\<^sub>y\<^sub>A\<^sub>n\<^sub>y"

(* 4 ************************************ 12 + 1 *)
text \<open>
   Now, we construct a concrete ``universe of ToyAny types'' by injection into a
sum type containing the class types. This type of ToyAny will be used as instance
for all respective type-variables. \<close>

(* 5 ************************************ 13 + 1 *)
datatype \<AA> = in\<^sub>A\<^sub>t\<^sub>o\<^sub>m "ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m"
                        | in\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e "ty\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e"
                        | in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
                        | in\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y "ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y"
                        | in\<^sub>T\<^sub>o\<^sub>y\<^sub>A\<^sub>n\<^sub>y "ty\<^sub>T\<^sub>o\<^sub>y\<^sub>A\<^sub>n\<^sub>y"

(* 6 ************************************ 14 + 1 *)
text \<open>
   Having fixed the object universe, we can introduce type synonyms that exactly correspond
to Toy types. Again, we exploit that our representation of Toy is a ``shallow embedding'' with a
one-to-one correspondance of Toy-types to types of the meta-language HOL. \<close>

(* 7 ************************************ 15 + 5 *)
type_synonym Atom = "\<langle>\<langle>ty\<^sub>A\<^sub>t\<^sub>o\<^sub>m\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym Molecule = "\<langle>\<langle>ty\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym Person = "\<langle>\<langle>ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym Galaxy = "\<langle>\<langle>ty\<^sub>G\<^sub>a\<^sub>l\<^sub>a\<^sub>x\<^sub>y\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"
type_synonym ToyAny = "\<langle>\<langle>ty\<^sub>T\<^sub>o\<^sub>y\<^sub>A\<^sub>n\<^sub>y\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>"

(* 8 ************************************ 20 + 3 *)
definition "oid\<^sub>A\<^sub>t\<^sub>o\<^sub>m_0___boss = 0"
definition "oid\<^sub>M\<^sub>o\<^sub>l\<^sub>e\<^sub>c\<^sub>u\<^sub>l\<^sub>e_0___boss = 0"
definition "oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss = 0"

(* 9 ************************************ 23 + 2 *)
definition "switch\<^sub>2_01 = (\<lambda> [x0 , x1] \<Rightarrow> (x0 , x1))"
definition "switch\<^sub>2_10 = (\<lambda> [x0 , x1] \<Rightarrow> (x1 , x0))"

(* 10 ************************************ 25 + 3 *)
definition "oid1 = 1"
definition "oid2 = 2"
definition "inst_assoc1 = (\<lambda>oid_class to_from oid. ((case (deref_assocs_list ((to_from::oid list list \<Rightarrow> oid list \<times> oid list)) ((oid::oid)) ((drop ((((map_of_list ([(oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss , (List.map ((\<lambda>(x , y). [x , y]) o switch\<^sub>2_01) ([[[oid1] , [oid2]]])))]))) ((oid_class::oid))))))) of Nil \<Rightarrow> None
    | l \<Rightarrow> (Some (l)))::oid list option))"

(* 11 ************************************ 28 + 0 *)

(* 12 ************************************ 28 + 2 *)
definition "oid3 = 3"
definition "inst_assoc3 = (\<lambda>oid_class to_from oid. ((case (deref_assocs_list ((to_from::oid list list \<Rightarrow> oid list \<times> oid list)) ((oid::oid)) ((drop ((((map_of_list ([]))) ((oid_class::oid))))))) of Nil \<Rightarrow> None
    | l \<Rightarrow> (Some (l)))::oid list option))"

(* 13 ************************************ 30 + 0 *)

(* 14 ************************************ 30 + 5 *)
definition "oid4 = 4"
definition "oid5 = 5"
definition "oid6 = 6"
definition "oid7 = 7"
definition "inst_assoc4 = (\<lambda>oid_class to_from oid. ((case (deref_assocs_list ((to_from::oid list list \<Rightarrow> oid list \<times> oid list)) ((oid::oid)) ((drop ((((map_of_list ([(oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss , (List.map ((\<lambda>(x , y). [x , y]) o switch\<^sub>2_01) ([[[oid7] , [oid6]] , [[oid6] , [oid1]] , [[oid4] , [oid5]]])))]))) ((oid_class::oid))))))) of Nil \<Rightarrow> None
    | l \<Rightarrow> (Some (l)))::oid list option))"

(* 15 ************************************ 35 + 0 *)

(* 16 ************************************ 35 + 1 *)
locale state_\<sigma>\<^sub>1 =
fixes "oid4" :: "nat"
fixes "oid5" :: "nat"
fixes "oid6" :: "nat"
fixes "oid1" :: "nat"
fixes "oid7" :: "nat"
fixes "oid2" :: "nat"
assumes distinct_oid: "(distinct ([oid4 , oid5 , oid6 , oid1 , oid7 , oid2]))"
fixes "\<sigma>\<^sub>1_object0\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "\<sigma>\<^sub>1_object0" :: "\<cdot>Person"
assumes \<sigma>\<^sub>1_object0_def: "\<sigma>\<^sub>1_object0 = (\<lambda>_. \<lfloor>\<lfloor>\<sigma>\<^sub>1_object0\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
fixes "\<sigma>\<^sub>1_object1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "\<sigma>\<^sub>1_object1" :: "\<cdot>Person"
assumes \<sigma>\<^sub>1_object1_def: "\<sigma>\<^sub>1_object1 = (\<lambda>_. \<lfloor>\<lfloor>\<sigma>\<^sub>1_object1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
fixes "\<sigma>\<^sub>1_object2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "\<sigma>\<^sub>1_object2" :: "\<cdot>Person"
assumes \<sigma>\<^sub>1_object2_def: "\<sigma>\<^sub>1_object2 = (\<lambda>_. \<lfloor>\<lfloor>\<sigma>\<^sub>1_object2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1" :: "\<cdot>Person"
assumes X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1_def: "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 = (\<lambda>_. \<lfloor>\<lfloor>X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
fixes "\<sigma>\<^sub>1_object4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "\<sigma>\<^sub>1_object4" :: "\<cdot>Person"
assumes \<sigma>\<^sub>1_object4_def: "\<sigma>\<^sub>1_object4 = (\<lambda>_. \<lfloor>\<lfloor>\<sigma>\<^sub>1_object4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2" :: "\<cdot>Person"
assumes X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2_def: "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 = (\<lambda>_. \<lfloor>\<lfloor>X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
begin
definition "\<sigma>\<^sub>1 = (state.make ((Map.empty (oid4 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (\<sigma>\<^sub>1_object0\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid5 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (\<sigma>\<^sub>1_object1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid6 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (\<sigma>\<^sub>1_object2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid1 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid7 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (\<sigma>\<^sub>1_object4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid2 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))))) ((map_of_list ([(oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss , (List.map ((\<lambda>(x , y). [x , y]) o switch\<^sub>2_01) ([[[oid4] , [oid2]] , [[oid6] , [oid4]] , [[oid1] , [oid6]] , [[oid7] , [oid3]]])))]))))"

lemma perm_\<sigma>\<^sub>1 : "\<sigma>\<^sub>1 = (state.make ((Map.empty (oid2 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid7 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (\<sigma>\<^sub>1_object4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid1 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid6 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (\<sigma>\<^sub>1_object2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid5 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (\<sigma>\<^sub>1_object1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid4 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (\<sigma>\<^sub>1_object0\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))))) ((assocs (\<sigma>\<^sub>1))))"
  apply(simp add: \<sigma>\<^sub>1_def)
  apply(subst (1) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (2) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (1) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (3) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (2) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (1) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (4) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (3) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (2) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (1) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (5) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (4) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (3) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (2) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (1) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
by(simp)
end

(* 17 ************************************ 36 + 1 *)
locale state_\<sigma>\<^sub>1' =
fixes "oid1" :: "nat"
fixes "oid2" :: "nat"
fixes "oid3" :: "nat"
assumes distinct_oid: "(distinct ([oid1 , oid2 , oid3]))"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1" :: "\<cdot>Person"
assumes X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1_def: "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 = (\<lambda>_. \<lfloor>\<lfloor>X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2" :: "\<cdot>Person"
assumes X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2_def: "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 = (\<lambda>_. \<lfloor>\<lfloor>X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3" :: "\<cdot>Person"
assumes X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3_def: "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 = (\<lambda>_. \<lfloor>\<lfloor>X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
begin
definition "\<sigma>\<^sub>1' = (state.make ((Map.empty (oid1 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid2 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid3 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))))) ((map_of_list ([(oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_0___boss , (List.map ((\<lambda>(x , y). [x , y]) o switch\<^sub>2_01) ([[[oid1] , [oid2]]])))]))))"

lemma perm_\<sigma>\<^sub>1' : "\<sigma>\<^sub>1' = (state.make ((Map.empty (oid3 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid2 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))) (oid1 \<mapsto> (in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n))))) ((assocs (\<sigma>\<^sub>1'))))"
  apply(simp add: \<sigma>\<^sub>1'_def)
  apply(subst (1) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (2) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
  apply(subst (1) fun_upd_twist, metis distinct_oid distinct_length_2_or_more)
by(simp)
end

(* 18 ************************************ 37 + 1 *)
locale pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>1' =
fixes "oid1" :: "nat"
fixes "oid2" :: "nat"
fixes "oid3" :: "nat"
fixes "oid4" :: "nat"
fixes "oid5" :: "nat"
fixes "oid6" :: "nat"
fixes "oid7" :: "nat"
assumes distinct_oid: "(distinct ([oid1 , oid2 , oid3 , oid4 , oid5 , oid6 , oid7]))"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1" :: "\<cdot>Person"
assumes X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1_def: "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 = (\<lambda>_. \<lfloor>\<lfloor>X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2" :: "\<cdot>Person"
assumes X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2_def: "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 = (\<lambda>_. \<lfloor>\<lfloor>X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3" :: "\<cdot>Person"
assumes X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3_def: "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 = (\<lambda>_. \<lfloor>\<lfloor>X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
fixes "\<sigma>\<^sub>1_object0\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "\<sigma>\<^sub>1_object0" :: "\<cdot>Person"
assumes \<sigma>\<^sub>1_object0_def: "\<sigma>\<^sub>1_object0 = (\<lambda>_. \<lfloor>\<lfloor>\<sigma>\<^sub>1_object0\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
fixes "\<sigma>\<^sub>1_object1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "\<sigma>\<^sub>1_object1" :: "\<cdot>Person"
assumes \<sigma>\<^sub>1_object1_def: "\<sigma>\<^sub>1_object1 = (\<lambda>_. \<lfloor>\<lfloor>\<sigma>\<^sub>1_object1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
fixes "\<sigma>\<^sub>1_object2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "\<sigma>\<^sub>1_object2" :: "\<cdot>Person"
assumes \<sigma>\<^sub>1_object2_def: "\<sigma>\<^sub>1_object2 = (\<lambda>_. \<lfloor>\<lfloor>\<sigma>\<^sub>1_object2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"
fixes "\<sigma>\<^sub>1_object4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" :: "ty\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n"
fixes "\<sigma>\<^sub>1_object4" :: "\<cdot>Person"
assumes \<sigma>\<^sub>1_object4_def: "\<sigma>\<^sub>1_object4 = (\<lambda>_. \<lfloor>\<lfloor>\<sigma>\<^sub>1_object4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<rfloor>\<rfloor>)"

assumes \<sigma>\<^sub>1: "(state_\<sigma>\<^sub>1 (oid4) (oid5) (oid6) (oid1) (oid7) (oid2) (\<sigma>\<^sub>1_object0\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n) (\<sigma>\<^sub>1_object0) (\<sigma>\<^sub>1_object1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n) (\<sigma>\<^sub>1_object1) (\<sigma>\<^sub>1_object2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n) (\<sigma>\<^sub>1_object2) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1) (\<sigma>\<^sub>1_object4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n) (\<sigma>\<^sub>1_object4) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2))"

assumes \<sigma>\<^sub>1': "(state_\<sigma>\<^sub>1' (oid1) (oid2) (oid3) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n) (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3))"
begin
interpretation state_\<sigma>\<^sub>1: state_\<sigma>\<^sub>1 "oid4" "oid5" "oid6" "oid1" "oid7" "oid2" "\<sigma>\<^sub>1_object0\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" "\<sigma>\<^sub>1_object0" "\<sigma>\<^sub>1_object1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" "\<sigma>\<^sub>1_object1" "\<sigma>\<^sub>1_object2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" "\<sigma>\<^sub>1_object2" "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1" "\<sigma>\<^sub>1_object4\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" "\<sigma>\<^sub>1_object4" "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"
by(rule \<sigma>\<^sub>1)

interpretation state_\<sigma>\<^sub>1': state_\<sigma>\<^sub>1' "oid1" "oid2" "oid3" "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1" "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2" "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n" "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3"
by(rule \<sigma>\<^sub>1')
end

end
