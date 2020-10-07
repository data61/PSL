(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Design_UML.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2015 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2015 IRT SystemX, France
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

chapter\<open>Example: The Employee Design Model\<close> (* UML part *)

theory
  Design_UML
imports
  "../../../UML_Main"
begin

text \<open>\label{ex:employee-design:uml}\<close>

section\<open>Introduction\<close>
text\<open>
  For certain concepts like classes and class-types, only a generic
  definition for its resulting semantics can be given. Generic means,
  there is a function outside HOL that ``compiles'' a concrete,
  closed-world class diagram into a ``theory'' of this data model,
  consisting of a bunch of definitions for classes, accessors, method,
  casts, and tests for actual types, as well as proofs for the
  fundamental properties of these operations in this concrete data
  model.\<close>

text\<open>Such generic function or ``compiler'' can be implemented in
  Isabelle on the ML level.  This has been done, for a semantics
  following the open-world assumption, for UML 2.0
  in~\cite{brucker.ea:extensible:2008-b, brucker:interactive:2007}. In
  this paper, we follow another approach for UML 2.4: we define the
  concepts of the compilation informally, and present a concrete
  example which is verified in Isabelle/HOL.\<close>

subsection\<open>Outlining the Example\<close>

text\<open>We are presenting here a ``design-model'' of the (slightly
modified) example Figure 7.3, page 20 of
the OCL standard~\cite{omg:ocl:2012}. To be precise, this theory contains the formalization of
the data-part covered by the UML class model (see \autoref{fig:person}):\<close>

text\<open>
\begin{figure}
  \centering\scalebox{.3}{\includegraphics{figures/person.png}}%
  \caption{A simple UML class model drawn from Figure 7.3,
  page 20 of~\cite{omg:ocl:2012}. \label{fig:person}}
\end{figure}
\<close>

text\<open>This means that the association (attached to the association class
\inlineocl{EmployeeRanking}) with the association ends \inlineocl+boss+ and \inlineocl+employees+ is implemented
by the attribute  \inlineocl+boss+ and the operation \inlineocl+employees+ (to be discussed in the OCL part
captured by the subsequent theory).
\<close>

section\<open>Example Data-Universe and its Infrastructure\<close>
text\<open>Ideally, the following is generated automatically from a UML class model.\<close>

text\<open>Our data universe  consists in the concrete class diagram just of node's,
and implicitly of the class object. Each class implies the existence of a class
type defined for the corresponding object representations as follows:\<close>

datatype type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n = mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid          (* the oid to the person itself *)
                            "int option" (* the attribute "salary" or null *)
                            "oid option" (* the attribute "boss" or null *)


datatype type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y = mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid          (* the oid to the oclany itself *)
                            "(int option \<times> oid option) option"
                                         (* the extensions to "person"; used to denote
                                            objects of actual type "person" casted to "oclany";
                                            in case of existence of several subclasses
                                            of oclany, sums of extensions have to be provided. *)

text\<open>Now, we construct a concrete ``universe of OclAny types'' by injection into a
sum type containing the class types. This type of OclAny will be used as instance
for all respective type-variables.\<close>

datatype \<AA> = in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y

text\<open>Having fixed the object universe, we can introduce type synonyms that exactly correspond
to OCL types. Again, we exploit that our representation of OCL is a ``shallow embedding'' with a
one-to-one correspondance of OCL-types to types of the meta-language HOL.\<close>
type_synonym Boolean     = " \<AA> Boolean"
type_synonym Integer     = " \<AA> Integer"
type_synonym Void        = " \<AA> Void"
type_synonym OclAny      = "(\<AA>, type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y option option) val"
type_synonym Person      = "(\<AA>, type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n option option) val"
type_synonym Set_Integer = "(\<AA>, int option option) Set"
type_synonym Set_Person  = "(\<AA>, type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n option option) Set"

text\<open>Just a little check:\<close>
typ "Boolean"

text\<open>To reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class ``oclany,'' \ie,
 each class type has to provide a function @{term oid_of} yielding the object id (oid) of the object.\<close>
instantiation type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: object
begin
   definition oid_of_type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def: "oid_of x = (case x of mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid _ _ \<Rightarrow> oid)"
   instance ..
end

instantiation type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: object
begin
   definition oid_of_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def: "oid_of x = (case x of mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid _ \<Rightarrow> oid)"
   instance ..
end

instantiation \<AA> :: object
begin
   definition oid_of_\<AA>_def: "oid_of x = (case x of
                                             in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person \<Rightarrow> oid_of person
                                           | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oclany \<Rightarrow> oid_of oclany)"
   instance ..
end




section\<open>Instantiation of the Generic Strict Equality\<close>
text\<open>We instantiate the referential equality
on \<open>Person\<close> and \<open>OclAny\<close>\<close>

overloading StrictRefEq \<equiv> "StrictRefEq :: [Person,Person] \<Rightarrow> Boolean"
begin
  definition StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n   : "(x::Person) \<doteq> y  \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
end

overloading StrictRefEq \<equiv> "StrictRefEq :: [OclAny,OclAny] \<Rightarrow> Boolean"
begin
  definition StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y   : "(x::OclAny) \<doteq> y  \<equiv> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y"
end

lemmas cps23 = 
    cp_StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t[of "x::Person" "y::Person" "\<tau>",
                         simplified StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n[symmetric]]
    cp_intro(9)         [of "P::Person \<Rightarrow>Person""Q::Person \<Rightarrow>Person",
                         simplified StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n[symmetric] ]
    StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def      [of "x::Person" "y::Person",
                         simplified StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n[symmetric]]
    StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_defargs  [of _ "x::Person" "y::Person",
                         simplified StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n[symmetric]]
    StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_strict1
                        [of "x::Person",
                         simplified StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n[symmetric]]
    StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_strict2
                        [of "x::Person",
                         simplified StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n[symmetric]]
  for x y \<tau> P Q
text\<open>For each Class \emph{C}, we will have a casting operation \inlineocl{.oclAsType($C$)},
   a test on the actual type \inlineocl{.oclIsTypeOf($C$)} as well as its relaxed form
   \inlineocl{.oclIsKindOf($C$)} (corresponding exactly to Java's \verb+instanceof+-operator.
\<close>
text\<open>Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
\<close>


section\<open>OclAsType\<close>
subsection\<open>Definition\<close>

consts OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> OclAny" ("(_) .oclAsType'(OclAny')")
consts OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Person" ("(_) .oclAsType'(Person')")

definition "OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> = (\<lambda>u. \<lfloor>case u of in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y a \<Rightarrow> a
                                            | in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid a b) \<Rightarrow> mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<lfloor>(a,b)\<rfloor>\<rfloor>)"

lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_some: "OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> x \<noteq> None"
by(simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def)

overloading OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: OclAny \<Rightarrow> OclAny"
begin
  definition OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny:
        "(X::OclAny) .oclAsType(OclAny) \<equiv> X"
end

overloading OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: Person \<Rightarrow> OclAny"
begin
  definition OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person:
        "(X::Person) .oclAsType(OclAny) \<equiv>
                   (\<lambda>\<tau>. case X \<tau> of
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> null \<tau>
                            | \<lfloor>\<lfloor>mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid a b \<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>  (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<lfloor>(a,b)\<rfloor>) \<rfloor>\<rfloor>)"
end

definition "OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> = 
                   (\<lambda>u. case u of in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n p \<Rightarrow> \<lfloor>p\<rfloor>
                            | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<lfloor>(a,b)\<rfloor>) \<Rightarrow> \<lfloor>mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid a b\<rfloor>
                            | _ \<Rightarrow> None)"

overloading OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: OclAny \<Rightarrow> Person"
begin
  definition OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny:
        "(X::OclAny) .oclAsType(Person) \<equiv>
                   (\<lambda>\<tau>. case X \<tau> of
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> null \<tau>
                            | \<lfloor>\<lfloor>mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow>  invalid \<tau>   \<comment> \<open>down-cast exception\<close>
                            | \<lfloor>\<lfloor>mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<lfloor>(a,b)\<rfloor> \<rfloor>\<rfloor> \<Rightarrow>  \<lfloor>\<lfloor>mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid a b \<rfloor>\<rfloor>)"
end

overloading OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: Person \<Rightarrow> Person"
begin
  definition OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person:
        "(X::Person) .oclAsType(Person) \<equiv> X "  (* to avoid identity for null ? *)
end
text_raw\<open>\isatagafp\<close>

lemmas [simp] =
 OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny
 OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
subsection\<open>Context Passing\<close>

lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person)::Person) .oclAsType(OclAny))"
by(rule cpI1, simp_all add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny)::OclAny) .oclAsType(OclAny))"
by(rule cpI1, simp_all add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person)::Person) .oclAsType(Person))"
by(rule cpI1, simp_all add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny)::OclAny) .oclAsType(Person))"
by(rule cpI1, simp_all add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)

lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person)::OclAny) .oclAsType(OclAny))"
by(rule cpI1, simp_all add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
lemma cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny)::Person) .oclAsType(OclAny))"
by(rule cpI1, simp_all add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::Person)::OclAny) .oclAsType(Person))"
by(rule cpI1, simp_all add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X. (P (X::OclAny)::Person) .oclAsType(Person))"
by(rule cpI1, simp_all add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)

lemmas [simp] =
 cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person
 cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
 cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person
 cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny

 cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny
 cp_OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person
 cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny
 cp_OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person

text_raw\<open>\endisatagafp\<close>

subsection\<open>Execution with Invalid or Null as Argument\<close>

lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_strict : "(invalid::OclAny) .oclAsType(OclAny) = invalid" by(simp)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_nullstrict : "(null::OclAny) .oclAsType(OclAny) = null" by(simp)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_strict[simp] : "(invalid::Person) .oclAsType(OclAny) = invalid"
      by(rule ext, simp add: bot_option_def invalid_def OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_nullstrict[simp] : "(null::Person) .oclAsType(OclAny) = null"
      by(rule ext, simp add: null_fun_def null_option_def bot_option_def OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_strict[simp] : "(invalid::OclAny) .oclAsType(Person) = invalid"
      by(rule ext, simp add: bot_option_def invalid_def  OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_nullstrict[simp] : "(null::OclAny) .oclAsType(Person) = null"
      by(rule ext, simp add: null_fun_def null_option_def bot_option_def  OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_strict : "(invalid::Person) .oclAsType(Person) = invalid"  by(simp)
lemma OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_nullstrict : "(null::Person) .oclAsType(Person) = null" by(simp)

section\<open>OclIsTypeOf\<close>

subsection\<open>Definition\<close>

consts OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsTypeOf'(OclAny')")
consts OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsTypeOf'(Person')")

overloading OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: OclAny \<Rightarrow> Boolean"
begin
  definition OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny:
        "(X::OclAny) .oclIsTypeOf(OclAny) \<equiv>
                   (\<lambda>\<tau>. case X \<tau> of
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>  \<comment> \<open>invalid ??\<close>
                            | \<lfloor>\<lfloor>mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow> true \<tau>
                            | \<lfloor>\<lfloor>mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<lfloor>_\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> false \<tau>)"
end

lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny':
         "(X::OclAny) .oclIsTypeOf(OclAny) = 
                    (\<lambda> \<tau>. if \<tau> \<Turnstile> \<upsilon> X then (case X \<tau> of
                                              \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>  \<comment> \<open>invalid ??\<close>
                                           | \<lfloor>\<lfloor>mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow> true \<tau>
                                           | \<lfloor>\<lfloor>mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<lfloor>_\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> false \<tau>)
                                           else invalid \<tau>)"
       apply(rule ext, simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
       by(case_tac "\<tau> \<Turnstile> \<upsilon> X", auto simp: foundation18' bot_option_def)

interpretation OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny : 
       profile_mono_schemeV 
       "OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y::OclAny \<Rightarrow> Boolean" 
       "\<lambda> X. (case X of
                    \<lfloor>None\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>True\<rfloor>\<rfloor>  \<comment> \<open>invalid ??\<close>
                  | \<lfloor>\<lfloor>mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid None \<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>True\<rfloor>\<rfloor>
                  | \<lfloor>\<lfloor>mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<lfloor>_\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> \<lfloor>\<lfloor>False\<rfloor>\<rfloor>)"                     
      apply(unfold_locales, simp add: atomize_eq, rule ext)
      by(auto simp:  OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny' OclValid_def true_def false_def 
              split: option.split type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split)

overloading OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: Person \<Rightarrow> Boolean"
begin
  definition OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person:
        "(X::Person) .oclIsTypeOf(OclAny) \<equiv>
                   (\<lambda>\<tau>. case X \<tau> of
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>    \<comment> \<open>invalid ??\<close>
                            | \<lfloor>\<lfloor> _ \<rfloor>\<rfloor> \<Rightarrow> false \<tau>)  \<comment> \<open>must have actual type \<open>Person\<close> otherwise\<close>"
end

overloading OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: OclAny \<Rightarrow> Boolean"
begin
  definition OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny:
        "(X::OclAny) .oclIsTypeOf(Person) \<equiv>
                   (\<lambda>\<tau>. case X \<tau> of
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>
                            | \<lfloor>\<lfloor>mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow> false \<tau>
                            | \<lfloor>\<lfloor>mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<lfloor>_\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> true \<tau>)"
end

overloading OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: Person \<Rightarrow> Boolean"
begin
  definition OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person:
        "(X::Person) .oclIsTypeOf(Person) \<equiv>
                   (\<lambda>\<tau>. case X \<tau> of
                              \<bottom> \<Rightarrow> invalid \<tau>
                            | _ \<Rightarrow> true \<tau>)" (* for (* \<lfloor>\<lfloor> _ \<rfloor>\<rfloor> \<Rightarrow> true \<tau> *) : must have actual type Node otherwise  *)
end
text_raw\<open>\isatagafp\<close>
subsection\<open>Context Passing\<close>

lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::Person)::Person).oclIsTypeOf(OclAny))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::OclAny)::OclAny).oclIsTypeOf(OclAny))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::Person)::Person).oclIsTypeOf(Person))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::OclAny)::OclAny).oclIsTypeOf(Person))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)


lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::Person)::OclAny).oclIsTypeOf(OclAny))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
lemma cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::OclAny)::Person).oclIsTypeOf(OclAny))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::Person)::OclAny).oclIsTypeOf(Person))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::OclAny)::Person).oclIsTypeOf(Person))"
by(rule cpI1, simp_all add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)

lemmas [simp] =
 cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person
 cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
 cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person
 cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny

 cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny
 cp_OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person
 cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny
 cp_OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person
text_raw\<open>\endisatagafp\<close>

subsection\<open>Execution with Invalid or Null as Argument\<close>

lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_strict1[simp]:
     "(invalid::OclAny) .oclIsTypeOf(OclAny) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_strict2[simp]:
     "(null::OclAny) .oclIsTypeOf(OclAny) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_strict1[simp]:
     "(invalid::Person) .oclIsTypeOf(OclAny) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_strict2[simp]:
     "(null::Person) .oclIsTypeOf(OclAny) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_strict1[simp]:
     "(invalid::OclAny) .oclIsTypeOf(Person) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_strict2[simp]:
     "(null::OclAny) .oclIsTypeOf(Person) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_strict1[simp]:
     "(invalid::Person) .oclIsTypeOf(Person) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)
lemma OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_strict2[simp]:
     "(null::Person) .oclIsTypeOf(Person) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)

subsection\<open>Up Down Casting\<close>

lemma actualType_larger_staticType:
assumes isdef: "\<tau> \<Turnstile> (\<delta> X)"
shows          "\<tau> \<Turnstile> (X::Person) .oclIsTypeOf(OclAny) \<triangleq> false"
using isdef
by(auto simp : null_option_def bot_option_def
               OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person foundation22 foundation16)

lemma down_cast_type:
assumes isOclAny: "\<tau> \<Turnstile> (X::OclAny) .oclIsTypeOf(OclAny)"
and     non_null: "\<tau> \<Turnstile> (\<delta> X)"
shows             "\<tau> \<Turnstile> (X .oclAsType(Person)) \<triangleq> invalid"
using isOclAny non_null
apply(auto simp : bot_fun_def null_fun_def null_option_def bot_option_def null_def invalid_def
                  OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny foundation22 foundation16
           split: option.split type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
by(simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny  OclValid_def false_def true_def)

lemma down_cast_type':
assumes isOclAny: "\<tau> \<Turnstile> (X::OclAny) .oclIsTypeOf(OclAny)"
and     non_null: "\<tau> \<Turnstile> (\<delta> X)"
shows             "\<tau> \<Turnstile> not (\<upsilon> (X .oclAsType(Person)))"
by(rule foundation15[THEN iffD1], simp add: down_cast_type[OF assms])

lemma up_down_cast :
assumes isdef: "\<tau> \<Turnstile> (\<delta> X)"
shows "\<tau> \<Turnstile> ((X::Person) .oclAsType(OclAny) .oclAsType(Person) \<triangleq> X)"
using isdef
by(auto simp : null_fun_def null_option_def bot_option_def null_def invalid_def
               OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny foundation22 foundation16
        split: option.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)


lemma up_down_cast_Person_OclAny_Person [simp]:
shows "((X::Person) .oclAsType(OclAny) .oclAsType(Person) = X)"
 apply(rule ext, rename_tac \<tau>)
 apply(rule foundation22[THEN iffD1])
 apply(case_tac "\<tau> \<Turnstile> (\<delta> X)", simp add: up_down_cast)
 apply(simp add: defined_split, elim disjE)
 apply(erule StrongEq_L_subst2_rev, simp, simp)+
done

lemma up_down_cast_Person_OclAny_Person':
assumes "\<tau> \<Turnstile> \<upsilon> X"
shows   "\<tau> \<Turnstile> (((X :: Person) .oclAsType(OclAny) .oclAsType(Person)) \<doteq> X)"
 apply(simp only: up_down_cast_Person_OclAny_Person StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n)
by(rule StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym, simp add: assms)

lemma up_down_cast_Person_OclAny_Person'': 
assumes "\<tau> \<Turnstile> \<upsilon> (X :: Person)"
shows   "\<tau> \<Turnstile> (X .oclIsTypeOf(Person) implies (X .oclAsType(OclAny) .oclAsType(Person)) \<doteq> X)"
 apply(simp add: OclValid_def)
 apply(subst cp_OclImplies)
 apply(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym[OF assms, simplified OclValid_def])
 apply(subst cp_OclImplies[symmetric])
by simp


section\<open>OclIsKindOf\<close>
subsection\<open>Definition\<close>

consts OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsKindOf'(OclAny')")
consts OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "'\<alpha> \<Rightarrow> Boolean" ("(_).oclIsKindOf'(Person')")

overloading OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: OclAny \<Rightarrow> Boolean"
begin
  definition OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny:
        "(X::OclAny) .oclIsKindOf(OclAny) \<equiv>
                   (\<lambda>\<tau>. case X \<tau> of
                              \<bottom> \<Rightarrow> invalid \<tau>
                            | _ \<Rightarrow> true \<tau>)"
end

overloading OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<equiv> "OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: Person \<Rightarrow> Boolean"
begin
  definition OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person:
        "(X::Person) .oclIsKindOf(OclAny) \<equiv>
                   (\<lambda>\<tau>. case X \<tau> of
                              \<bottom> \<Rightarrow> invalid \<tau>
                            | _\<Rightarrow> true \<tau>)"
(* for (* \<lfloor>\<lfloor>mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n e oid _ \<rfloor>\<rfloor> \<Rightarrow> true \<tau> *) :  must have actual type Person otherwise  *)
end

overloading OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: OclAny \<Rightarrow> Boolean"
begin
  definition OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny:
        "(X::OclAny) .oclIsKindOf(Person) \<equiv>
                   (\<lambda>\<tau>. case X \<tau> of
                              \<bottom>   \<Rightarrow> invalid \<tau>
                            | \<lfloor>\<bottom>\<rfloor> \<Rightarrow> true \<tau>
                            | \<lfloor>\<lfloor>mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<bottom> \<rfloor>\<rfloor> \<Rightarrow> false \<tau>
                            | \<lfloor>\<lfloor>mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<lfloor>_\<rfloor> \<rfloor>\<rfloor> \<Rightarrow> true \<tau>)"
end

overloading OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<equiv> "OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: Person \<Rightarrow> Boolean"
begin
 definition OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person:
        "(X::Person) .oclIsKindOf(Person) \<equiv>
                   (\<lambda>\<tau>. case X \<tau> of
                              \<bottom> \<Rightarrow> invalid \<tau>
                            | _ \<Rightarrow> true \<tau>)"
end
text_raw\<open>\isatagafp\<close>
subsection\<open>Context Passing\<close>

lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::Person)::Person).oclIsKindOf(OclAny))"
by(rule cpI1, simp_all add: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::OclAny)::OclAny).oclIsKindOf(OclAny))"
by(rule cpI1, simp_all add: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::Person)::Person).oclIsKindOf(Person))"
by(rule cpI1, simp_all add: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::OclAny)::OclAny).oclIsKindOf(Person))"
by(rule cpI1, simp_all add: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)

lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::Person)::OclAny).oclIsKindOf(OclAny))"
by(rule cpI1, simp_all add: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
lemma cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::OclAny)::Person).oclIsKindOf(OclAny))"
by(rule cpI1, simp_all add: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::Person)::OclAny).oclIsKindOf(Person))"
by(rule cpI1, simp_all add: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person: "cp P \<Longrightarrow> cp(\<lambda>X.(P(X::OclAny)::Person).oclIsKindOf(Person))"
by(rule cpI1, simp_all add: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)

lemmas [simp] =
 cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_Person
 cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_OclAny
 cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_Person
 cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_OclAny

 cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_OclAny
 cp_OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_Person
 cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_OclAny
 cp_OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_Person
text_raw\<open>\endisatagafp\<close>
subsection\<open>Execution with Invalid or Null as Argument\<close>

lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_strict1[simp] : "(invalid::OclAny) .oclIsKindOf(OclAny) = invalid"
by(rule ext, simp add: invalid_def bot_option_def
                       OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny_strict2[simp] : "(null::OclAny) .oclIsKindOf(OclAny) = true"
by(rule ext, simp add: null_fun_def null_option_def
                       OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_strict1[simp] : "(invalid::Person) .oclIsKindOf(OclAny) = invalid"
by(rule ext, simp add: bot_option_def invalid_def
                       OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person_strict2[simp] : "(null::Person) .oclIsKindOf(OclAny) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def
                       OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_strict1[simp]: "(invalid::OclAny) .oclIsKindOf(Person) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny_strict2[simp]: "(null::OclAny) .oclIsKindOf(Person) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_strict1[simp]: "(invalid::Person) .oclIsKindOf(Person) = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)
lemma OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person_strict2[simp]: "(null::Person) .oclIsKindOf(Person) = true"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def
                       OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)

subsection\<open>Up Down Casting\<close>

lemma actualKind_larger_staticKind:
assumes isdef: "\<tau> \<Turnstile> (\<delta> X)"
shows          "\<tau> \<Turnstile>  ((X::Person) .oclIsKindOf(OclAny) \<triangleq> true)"
using isdef
by(auto simp : bot_option_def
               OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person foundation22 foundation16)

lemma down_cast_kind:
assumes isOclAny: "\<not> (\<tau> \<Turnstile> ((X::OclAny).oclIsKindOf(Person)))"
and     non_null: "\<tau> \<Turnstile> (\<delta> X)"
shows             "\<tau> \<Turnstile> ((X .oclAsType(Person)) \<triangleq> invalid)"
using isOclAny non_null
apply(auto simp : bot_fun_def null_fun_def null_option_def bot_option_def null_def invalid_def
                  OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny foundation22 foundation16
           split: option.split type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y.split type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split)
by(simp add: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny  OclValid_def false_def true_def)

section\<open>OclAllInstances\<close>

text\<open>To denote OCL-types occurring in OCL expressions syntactically---as, for example,  as
``argument'' of \inlineisar{oclAllInstances()}---we use the inverses of the injection
functions into the object universes; we show that this is sufficient ``characterization.''\<close>

definition "Person \<equiv> OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>"
definition "OclAny \<equiv> OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>"
lemmas [simp] = Person_def OclAny_def

lemma OclAllInstances_generic\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec: "OclAllInstances_generic pre_post OclAny =
             (\<lambda>\<tau>.  Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e  \<lfloor>\<lfloor> Some ` OclAny ` ran (heap (pre_post \<tau>)) \<rfloor>\<rfloor>)"
proof -
 let ?S1 = "\<lambda>\<tau>. OclAny ` ran (heap (pre_post \<tau>))"
 let ?S2 = "\<lambda>\<tau>. ?S1 \<tau> - {None}"
 have B : "\<And>\<tau>. ?S2 \<tau> \<subseteq> ?S1 \<tau>" by auto
 have C : "\<And>\<tau>. ?S1 \<tau> \<subseteq> ?S2 \<tau>" by(auto simp: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_some)

 show ?thesis by(insert equalityI[OF B C], simp)
qed

lemma OclAllInstances_at_post\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec: "OclAny .allInstances() =
             (\<lambda>\<tau>.  Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e  \<lfloor>\<lfloor> Some ` OclAny ` ran (heap (snd \<tau>)) \<rfloor>\<rfloor>)"
unfolding OclAllInstances_at_post_def
by(rule OclAllInstances_generic\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec)

lemma OclAllInstances_at_pre\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec: "OclAny .allInstances@pre() =
             (\<lambda>\<tau>.  Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e  \<lfloor>\<lfloor> Some ` OclAny ` ran (heap (fst \<tau>)) \<rfloor>\<rfloor>) "
unfolding OclAllInstances_at_pre_def
by(rule OclAllInstances_generic\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_exec)

subsection\<open>OclIsTypeOf\<close>

lemma OclAny_allInstances_generic_oclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1:
assumes [simp]: "\<And>x. pre_post (x, x) = x"
shows "\<exists>\<tau>. (\<tau> \<Turnstile>     ((OclAllInstances_generic pre_post OclAny)->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsTypeOf(OclAny))))"
 apply(rule_tac x = \<tau>\<^sub>0 in exI, simp add: \<tau>\<^sub>0_def OclValid_def del: OclAllInstances_generic_def)
 apply(simp only: assms UML_Set.OclForall_def refl if_True
                  OclAllInstances_generic_defined[simplified OclValid_def])
 apply(simp only: OclAllInstances_generic_def)
 apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)

lemma OclAny_allInstances_at_post_oclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1:
"\<exists>\<tau>. (\<tau> \<Turnstile>     (OclAny .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsTypeOf(OclAny))))"
unfolding OclAllInstances_at_post_def
by(rule OclAny_allInstances_generic_oclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1, simp)

lemma OclAny_allInstances_at_pre_oclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1:
"\<exists>\<tau>. (\<tau> \<Turnstile>     (OclAny .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsTypeOf(OclAny))))"
unfolding OclAllInstances_at_pre_def
by(rule OclAny_allInstances_generic_oclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y1, simp)

lemma OclAny_allInstances_generic_oclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2:
assumes [simp]: "\<And>x. pre_post (x, x) = x"
shows "\<exists>\<tau>. (\<tau> \<Turnstile> not ((OclAllInstances_generic pre_post OclAny)->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsTypeOf(OclAny))))"
proof - fix oid a let ?t0 = "\<lparr>heap = Map.empty(oid \<mapsto> in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid \<lfloor>a\<rfloor>)),
                              assocs = Map.empty\<rparr>" show ?thesis
 apply(rule_tac x = "(?t0, ?t0)" in exI, simp add: OclValid_def del: OclAllInstances_generic_def)
 apply(simp only: UML_Set.OclForall_def refl if_True
                  OclAllInstances_generic_defined[simplified OclValid_def])
 apply(simp only: OclAllInstances_generic_def OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def)
 apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
 by(simp add: OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny OclNot_def OclAny_def)
qed

lemma OclAny_allInstances_at_post_oclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2:
"\<exists>\<tau>. (\<tau> \<Turnstile> not (OclAny .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsTypeOf(OclAny))))"
unfolding OclAllInstances_at_post_def
by(rule OclAny_allInstances_generic_oclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2, simp)

lemma OclAny_allInstances_at_pre_oclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2:
"\<exists>\<tau>. (\<tau> \<Turnstile> not (OclAny .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsTypeOf(OclAny))))"
unfolding OclAllInstances_at_pre_def
by(rule OclAny_allInstances_generic_oclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y2, simp)

lemma Person_allInstances_generic_oclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n:
"\<tau> \<Turnstile> ((OclAllInstances_generic pre_post Person)->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsTypeOf(Person)))"
 apply(simp add: OclValid_def del: OclAllInstances_generic_def)
 apply(simp only: UML_Set.OclForall_def refl if_True
                  OclAllInstances_generic_defined[simplified OclValid_def])
 apply(simp only: OclAllInstances_generic_def)
 apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp add: OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)

lemma Person_allInstances_at_post_oclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n:
"\<tau> \<Turnstile> (Person .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsTypeOf(Person)))"
unfolding OclAllInstances_at_post_def
by(rule Person_allInstances_generic_oclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n)

lemma Person_allInstances_at_pre_oclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n:
"\<tau> \<Turnstile> (Person .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsTypeOf(Person)))"
unfolding OclAllInstances_at_pre_def
by(rule Person_allInstances_generic_oclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n)

subsection\<open>OclIsKindOf\<close>
lemma OclAny_allInstances_generic_oclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y:
"\<tau> \<Turnstile> ((OclAllInstances_generic pre_post OclAny)->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsKindOf(OclAny)))"
 apply(simp add: OclValid_def del: OclAllInstances_generic_def)
 apply(simp only: UML_Set.OclForall_def refl if_True
                  OclAllInstances_generic_defined[simplified OclValid_def])
 apply(simp only: OclAllInstances_generic_def)
 apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp add: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny)

lemma OclAny_allInstances_at_post_oclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y:
"\<tau> \<Turnstile> (OclAny .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsKindOf(OclAny)))"
unfolding OclAllInstances_at_post_def
by(rule OclAny_allInstances_generic_oclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)

lemma OclAny_allInstances_at_pre_oclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y:
"\<tau> \<Turnstile> (OclAny .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsKindOf(OclAny)))"
unfolding OclAllInstances_at_pre_def
by(rule OclAny_allInstances_generic_oclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)

lemma Person_allInstances_generic_oclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y:
"\<tau> \<Turnstile> ((OclAllInstances_generic pre_post Person)->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsKindOf(OclAny)))"
 apply(simp add: OclValid_def del: OclAllInstances_generic_def)
 apply(simp only: UML_Set.OclForall_def refl if_True
                  OclAllInstances_generic_defined[simplified OclValid_def])
 apply(simp only: OclAllInstances_generic_def)
 apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp add: OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)

lemma Person_allInstances_at_post_oclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y:
"\<tau> \<Turnstile> (Person .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsKindOf(OclAny)))"
unfolding OclAllInstances_at_post_def
by(rule Person_allInstances_generic_oclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)

lemma Person_allInstances_at_pre_oclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y:
"\<tau> \<Turnstile> (Person .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsKindOf(OclAny)))"
unfolding OclAllInstances_at_pre_def
by(rule Person_allInstances_generic_oclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)

lemma Person_allInstances_generic_oclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n:
"\<tau> \<Turnstile> ((OclAllInstances_generic pre_post Person)->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsKindOf(Person)))"
 apply(simp add: OclValid_def del: OclAllInstances_generic_def)
 apply(simp only: UML_Set.OclForall_def refl if_True
                  OclAllInstances_generic_defined[simplified OclValid_def])
 apply(simp only: OclAllInstances_generic_def)
 apply(subst (1 2 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def)
by(simp add: OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person)

lemma Person_allInstances_at_post_oclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n:
"\<tau> \<Turnstile> (Person .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsKindOf(Person)))"
unfolding OclAllInstances_at_post_def
by(rule Person_allInstances_generic_oclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n)

lemma Person_allInstances_at_pre_oclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n:
"\<tau> \<Turnstile> (Person .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(X|X .oclIsKindOf(Person)))"
unfolding OclAllInstances_at_pre_def
by(rule Person_allInstances_generic_oclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n)

section\<open>The Accessors (any, boss, salary)\<close>
text\<open>\label{sec:edm-accessors}\<close>
text\<open>Should be generated entirely from a class-diagram.\<close>


subsection\<open>Definition\<close>

definition eval_extract :: "('\<AA>,('a::object) option option) val
                            \<Rightarrow> (oid \<Rightarrow> ('\<AA>,'c::null) val)
                            \<Rightarrow> ('\<AA>,'c::null) val"
where "eval_extract X f = (\<lambda> \<tau>. case X \<tau> of
                                    \<bottom> \<Rightarrow> invalid \<tau>   \<comment> \<open>exception propagation\<close>
                               | \<lfloor>  \<bottom> \<rfloor> \<Rightarrow> invalid \<tau> \<comment> \<open>dereferencing null pointer\<close>
                               | \<lfloor>\<lfloor> obj \<rfloor>\<rfloor> \<Rightarrow> f (oid_of obj) \<tau>)"


definition deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n :: "(\<AA> state \<times> \<AA> state \<Rightarrow> \<AA> state)
                             \<Rightarrow> (type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n \<Rightarrow> (\<AA>, 'c::null)val)
                             \<Rightarrow> oid
                             \<Rightarrow> (\<AA>, 'c::null)val"
where "deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n fst_snd f oid = (\<lambda>\<tau>. case (heap (fst_snd \<tau>)) oid of
                                              \<lfloor> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n obj \<rfloor> \<Rightarrow> f obj \<tau>
                                            | _              \<Rightarrow> invalid \<tau>)"



definition deref_oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y :: "(\<AA> state \<times> \<AA> state \<Rightarrow> \<AA> state)
                             \<Rightarrow> (type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y \<Rightarrow> (\<AA>, 'c::null)val)
                             \<Rightarrow> oid
                             \<Rightarrow> (\<AA>, 'c::null)val"
where "deref_oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y fst_snd f oid = (\<lambda>\<tau>. case (heap (fst_snd \<tau>)) oid of
                       \<lfloor> in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y obj \<rfloor> \<Rightarrow> f obj \<tau>
                     | _       \<Rightarrow> invalid \<tau>)"

text\<open>pointer undefined in state or not referencing a type conform object representation\<close>


definition "select\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y> f = (\<lambda> X. case X of
                     (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y _ \<bottom>) \<Rightarrow> null
                   | (mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y _ \<lfloor>any\<rfloor>) \<Rightarrow> f (\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>) any)"


definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> f = (\<lambda> X. case X of
                     (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n _ _ \<bottom>) \<Rightarrow> null  \<comment> \<open>object contains null pointer\<close>
                   | (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n _ _ \<lfloor>boss\<rfloor>) \<Rightarrow> f (\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>) boss)"


definition "select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> f = (\<lambda> X. case X of
                     (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n _ \<bottom> _) \<Rightarrow> null
                   | (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n _ \<lfloor>salary\<rfloor> _) \<Rightarrow> f (\<lambda>x _. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>) salary)"


definition "in_pre_state = fst"
definition "in_post_state = snd"

definition "reconst_basetype = (\<lambda> convert x. convert x)"

definition dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y> :: "OclAny \<Rightarrow> _"  ("(1(_).any)" 50)
  where "(X).any = eval_extract X
                     (deref_oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y in_post_state
                       (select\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>
                         reconst_basetype))"

definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S> :: "Person \<Rightarrow> Person"  ("(1(_).boss)" 50)
  where "(X).boss = eval_extract X
                      (deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n in_post_state
                        (select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>
                          (deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n in_post_state)))"

definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y> :: "Person \<Rightarrow> Integer"  ("(1(_).salary)" 50)
  where "(X).salary = eval_extract X
                        (deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n in_post_state
                          (select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>
                            reconst_basetype))"

definition dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>_at_pre :: "OclAny \<Rightarrow> _"  ("(1(_).any@pre)" 50)
  where "(X).any@pre = eval_extract X
                         (deref_oid\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y in_pre_state
                           (select\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>
                             reconst_basetype))"

definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre:: "Person \<Rightarrow> Person"  ("(1(_).boss@pre)" 50)
  where "(X).boss@pre = eval_extract X
                          (deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n in_pre_state
                            (select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>
                              (deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n in_pre_state)))"

definition dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre:: "Person \<Rightarrow> Integer"  ("(1(_).salary@pre)" 50)
  where "(X).salary@pre = eval_extract X
                            (deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n in_pre_state
                              (select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>
                                reconst_basetype))"

lemmas dot_accessor =
  dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>_def
  dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_def
  dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_def
  dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>_at_pre_def
  dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre_def
  dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre_def

subsection\<open>Context Passing\<close>

lemmas [simp] = eval_extract_def

lemma cp_dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>: "((X).any) \<tau> = ((\<lambda>_. X \<tau>).any) \<tau>" by (simp add: dot_accessor)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>: "((X).boss) \<tau> = ((\<lambda>_. X \<tau>).boss) \<tau>" by (simp add: dot_accessor)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>: "((X).salary) \<tau> = ((\<lambda>_. X \<tau>).salary) \<tau>" by (simp add: dot_accessor)

lemma cp_dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>_at_pre: "((X).any@pre) \<tau> = ((\<lambda>_. X \<tau>).any@pre) \<tau>" by (simp add: dot_accessor)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre: "((X).boss@pre) \<tau> = ((\<lambda>_. X \<tau>).boss@pre) \<tau>" by (simp add: dot_accessor)
lemma cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre: "((X).salary@pre) \<tau> = ((\<lambda>_. X \<tau>).salary@pre) \<tau>" by (simp add: dot_accessor)

lemmas cp_dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>_I [simp, intro!]=
       cp_dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>[THEN allI[THEN allI],
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]
lemmas cp_dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>_at_pre_I [simp, intro!]=
       cp_dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>_at_pre[THEN allI[THEN allI],
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]

lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_I [simp, intro!]=
       cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>[THEN allI[THEN allI],
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre_I [simp, intro!]=
       cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre[THEN allI[THEN allI],
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]

lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_I [simp, intro!]=
       cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>[THEN allI[THEN allI],
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]
lemmas cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre_I [simp, intro!]=
       cp_dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre[THEN allI[THEN allI],
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]

subsection\<open>Execution with Invalid or Null as Argument\<close>

lemma dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>_nullstrict [simp]: "(null).any = invalid"
by(rule ext, simp add: dot_accessor null_fun_def null_option_def bot_option_def null_def invalid_def)
lemma dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>_at_pre_nullstrict [simp] : "(null).any@pre = invalid"
by(rule ext, simp add: dot_accessor null_fun_def null_option_def bot_option_def null_def invalid_def)
lemma dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>_strict [simp] : "(invalid).any = invalid"
by(rule ext, simp add: dot_accessor null_fun_def null_option_def bot_option_def null_def invalid_def)
lemma dot\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<A>\<N>\<Y>_at_pre_strict [simp] : "(invalid).any@pre = invalid"
by(rule ext, simp add: dot_accessor null_fun_def null_option_def bot_option_def null_def invalid_def)


lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_nullstrict [simp]: "(null).boss = invalid"
by(rule ext, simp add: dot_accessor null_fun_def null_option_def bot_option_def null_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre_nullstrict [simp] : "(null).boss@pre = invalid"
by(rule ext, simp add: dot_accessor null_fun_def null_option_def bot_option_def null_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_strict [simp] : "(invalid).boss = invalid"
by(rule ext, simp add: dot_accessor null_fun_def null_option_def bot_option_def null_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre_strict [simp] : "(invalid).boss@pre = invalid"
by(rule ext, simp add: dot_accessor null_fun_def null_option_def bot_option_def null_def invalid_def)


lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_nullstrict [simp]: "(null).salary = invalid"
by(rule ext, simp add: dot_accessor null_fun_def null_option_def bot_option_def null_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre_nullstrict [simp] : "(null).salary@pre = invalid"
by(rule ext, simp add: dot_accessor null_fun_def null_option_def bot_option_def null_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_strict [simp] : "(invalid).salary = invalid"
by(rule ext, simp add: dot_accessor null_fun_def null_option_def bot_option_def null_def invalid_def)
lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre_strict [simp] : "(invalid).salary@pre = invalid"
by(rule ext, simp add: dot_accessor null_fun_def null_option_def bot_option_def null_def invalid_def)

subsection\<open>Representation in States\<close>

lemma dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_def_mono:"\<tau> \<Turnstile> \<delta>(X .boss) \<Longrightarrow> \<tau> \<Turnstile> \<delta>(X)"
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> invalid)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .boss)))" and \<tau> = "\<tau>" and x = "X" and y = "invalid"], simp add: foundation16')
  apply(case_tac "\<tau> \<Turnstile> (X \<triangleq> null)", insert StrongEq_L_subst2[where P = "(\<lambda>x. (\<delta> (x .boss)))" and \<tau> = "\<tau>" and x = "X" and y = "null"], simp add: foundation16')
by(simp add: defined_split)

lemma repr_boss:  
assumes A : "\<tau> \<Turnstile> \<delta>(x .boss)"
shows      "is_represented_in_state in_post_state (x .boss) Person \<tau>"
         apply(insert A[simplified foundation16]
                      A[THEN dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_def_mono, simplified foundation16])
         unfolding is_represented_in_state_def
                   dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_def eval_extract_def select\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_def in_post_state_def
         by(auto simp: deref_oid\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def bot_fun_def bot_option_def null_option_def null_fun_def invalid_def
                       OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def image_def ran_def
                 split: type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n.split option.split \<AA>.split)

lemma repr_bossX : 
assumes A: "\<tau> \<Turnstile> \<delta>(x .boss)"
shows "\<tau> \<Turnstile> ((Person .allInstances()) ->includes\<^sub>S\<^sub>e\<^sub>t(x .boss))"
proof -
  have B : "\<And>S f. (x .boss) \<tau> \<in> (Some ` f ` S) \<Longrightarrow>
                  (x .boss) \<tau> \<in> (Some ` (f ` S - {None}))"
            apply(auto simp: image_def ran_def, metis)
  by(insert A[simplified foundation16], simp add: null_option_def bot_option_def)
  show ?thesis
         apply(insert repr_boss[OF A] OclAllInstances_at_post_defined[where H = Person and \<tau> = \<tau>])
         unfolding is_represented_in_state_def OclValid_def
                   OclAllInstances_at_post_def OclAllInstances_generic_def OclIncludes_def
                   in_post_state_def
         apply(simp add: A[THEN foundation20, simplified OclValid_def])
         apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp, metis bot_option_def option.distinct(1))
  by(simp add: image_comp B true_def)
qed

section\<open>A Little Infra-structure on Example States\<close>

text\<open>
The example we are defining in this section comes from the figure~\ref{fig:edm1_system-states}.
\begin{figure}
\includegraphics[width=\textwidth]{figures/pre-post.pdf}
\caption{(a) pre-state $\sigma_1$ and
  (b) post-state $\sigma_1'$.}
\label{fig:edm1_system-states}
\end{figure}
\<close>

text_raw\<open>\isatagafp\<close>

definition OclInt1000 ("\<one>\<zero>\<zero>\<zero>") where "OclInt1000 = (\<lambda> _ . \<lfloor>\<lfloor>1000\<rfloor>\<rfloor>)"
definition OclInt1200 ("\<one>\<two>\<zero>\<zero>") where "OclInt1200 = (\<lambda> _ . \<lfloor>\<lfloor>1200\<rfloor>\<rfloor>)"
definition OclInt1300 ("\<one>\<three>\<zero>\<zero>") where "OclInt1300 = (\<lambda> _ . \<lfloor>\<lfloor>1300\<rfloor>\<rfloor>)"
definition OclInt1800 ("\<one>\<eight>\<zero>\<zero>") where "OclInt1800 = (\<lambda> _ . \<lfloor>\<lfloor>1800\<rfloor>\<rfloor>)"
definition OclInt2600 ("\<two>\<six>\<zero>\<zero>") where "OclInt2600 = (\<lambda> _ . \<lfloor>\<lfloor>2600\<rfloor>\<rfloor>)"
definition OclInt2900 ("\<two>\<nine>\<zero>\<zero>") where "OclInt2900 = (\<lambda> _ . \<lfloor>\<lfloor>2900\<rfloor>\<rfloor>)"
definition OclInt3200 ("\<three>\<two>\<zero>\<zero>") where "OclInt3200 = (\<lambda> _ . \<lfloor>\<lfloor>3200\<rfloor>\<rfloor>)"
definition OclInt3500 ("\<three>\<five>\<zero>\<zero>") where "OclInt3500 = (\<lambda> _ . \<lfloor>\<lfloor>3500\<rfloor>\<rfloor>)"

definition "oid0 \<equiv> 0"
definition "oid1 \<equiv> 1"
definition "oid2 \<equiv> 2"
definition "oid3 \<equiv> 3"
definition "oid4 \<equiv> 4"
definition "oid5 \<equiv> 5"
definition "oid6 \<equiv> 6"
definition "oid7 \<equiv> 7"
definition "oid8 \<equiv> 8"

definition "person1 \<equiv> mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid0 \<lfloor>1300\<rfloor> \<lfloor>oid1\<rfloor>"
definition "person2 \<equiv> mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid1 \<lfloor>1800\<rfloor> \<lfloor>oid1\<rfloor>"
definition "person3 \<equiv> mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid2 None None"
definition "person4 \<equiv> mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid3 \<lfloor>2900\<rfloor> None"
definition "person5 \<equiv> mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid4 \<lfloor>3500\<rfloor> None"
definition "person6 \<equiv> mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid5 \<lfloor>2500\<rfloor> \<lfloor>oid6\<rfloor>"
definition "person7 \<equiv> mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid6 \<lfloor>(\<lfloor>3200\<rfloor>, \<lfloor>oid6\<rfloor>)\<rfloor>"
definition "person8 \<equiv> mk\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y oid7 None"
definition "person9 \<equiv> mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid8 \<lfloor>0\<rfloor> None"

definition
      "\<sigma>\<^sub>1  \<equiv> \<lparr> heap = Map.empty(oid0 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid0 \<lfloor>1000\<rfloor> \<lfloor>oid1\<rfloor>))
                           (oid1 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid1 \<lfloor>1200\<rfloor>  None))
                           \<^cancel>\<open>oid2\<close>
                           (oid3 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid3 \<lfloor>2600\<rfloor> \<lfloor>oid4\<rfloor>))
                           (oid4 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person5)
                           (oid5 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n (mk\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n oid5 \<lfloor>2300\<rfloor> \<lfloor>oid3\<rfloor>))
                           \<^cancel>\<open>oid6\<close>
                           \<^cancel>\<open>oid7\<close>
                           (oid8 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person9),
               assocs = Map.empty \<rparr>"

definition
      "\<sigma>\<^sub>1' \<equiv> \<lparr> heap = Map.empty(oid0 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person1)
                           (oid1 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person2)
                           (oid2 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person3)
                           (oid3 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person4)
                           \<^cancel>\<open>oid4\<close>
                           (oid5 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person6)
                           (oid6 \<mapsto> in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y person7)
                           (oid7 \<mapsto> in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y person8)
                           (oid8 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person9),
               assocs = Map.empty \<rparr>"

definition "\<sigma>\<^sub>0 \<equiv> \<lparr> heap = Map.empty, assocs = Map.empty \<rparr>"


lemma basic_\<tau>_wff: "WFF(\<sigma>\<^sub>1,\<sigma>\<^sub>1')"
by(auto simp: WFF_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def
              oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def
              oid_of_\<AA>_def oid_of_type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def oid_of_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def
              person1_def person2_def person3_def person4_def
              person5_def person6_def person7_def person8_def person9_def)

lemma [simp,code_unfold]: "dom (heap \<sigma>\<^sub>1) = {oid0,oid1\<^cancel>\<open>,oid2\<close>,oid3,oid4,oid5\<^cancel>\<open>,oid6,oid7\<close>,oid8}"
by(auto simp: \<sigma>\<^sub>1_def)

lemma [simp,code_unfold]: "dom (heap \<sigma>\<^sub>1') = {oid0,oid1,oid2,oid3\<^cancel>\<open>,oid4\<close>,oid5,oid6,oid7,oid8}"
by(auto simp: \<sigma>\<^sub>1'_def)

text_raw\<open>\isatagafp\<close>

definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 :: Person \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person1 \<rfloor>\<rfloor>"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 :: Person \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person2 \<rfloor>\<rfloor>"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 :: Person \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person3 \<rfloor>\<rfloor>"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 :: Person \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person4 \<rfloor>\<rfloor>"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 :: Person \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person5 \<rfloor>\<rfloor>"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 :: Person \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person6 \<rfloor>\<rfloor>"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 :: OclAny \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person7 \<rfloor>\<rfloor>"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 :: OclAny \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person8 \<rfloor>\<rfloor>"
definition "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 :: Person \<equiv> \<lambda> _ .\<lfloor>\<lfloor> person9 \<rfloor>\<rfloor>"

lemma [code_unfold]: "((x::Person) \<doteq> y) = StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y" by(simp only: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n)
lemma [code_unfold]: "((x::OclAny) \<doteq> y) = StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y" by(simp only: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y)

lemmas [simp,code_unfold] =
 OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny
 OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person
 OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny
 OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person

 OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny
 OclIsTypeOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person
 OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny
 OclIsTypeOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person

 OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_OclAny
 OclIsKindOf\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person
 OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_OclAny
 OclIsKindOf\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_Person
text_raw\<open>\endisatagafp\<close>

Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .salary    <> \<one>\<zero>\<zero>\<zero>)"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .salary    \<doteq> \<one>\<three>\<zero>\<zero>)"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .salary@pre     \<doteq> \<one>\<zero>\<zero>\<zero>)"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .salary@pre     <> \<one>\<three>\<zero>\<zero>)"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .boss   <> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1)"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .boss .salary   \<doteq> \<one>\<eight>\<zero>\<zero>)"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .boss .boss  <> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1)"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .boss .boss  \<doteq> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2)"
Assert "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .boss@pre .salary  \<doteq> \<one>\<eight>\<zero>\<zero>)"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .boss@pre .salary@pre  \<doteq> \<one>\<two>\<zero>\<zero>)"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .boss@pre .salary@pre  <> \<one>\<eight>\<zero>\<zero>)"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .boss@pre  \<doteq> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2)"
Assert "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .boss@pre .boss  \<doteq> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2)"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .boss@pre .boss@pre  \<doteq> null)"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile> not(\<upsilon>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .boss@pre .boss@pre .boss@pre))"

lemma "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .oclIsMaintained())"
by(simp add: OclValid_def OclIsMaintained_def
             \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def
             X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1_def person1_def
             oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def
             oid_of_option_def oid_of_type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)

lemma "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>    ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .oclAsType(OclAny) .oclAsType(Person)) \<doteq> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1)"
by(rule up_down_cast_Person_OclAny_Person', simp add: X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1_def)
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>     (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .oclIsTypeOf(Person))"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>  not(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .oclIsTypeOf(OclAny))"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>     (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .oclIsKindOf(Person))"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>     (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .oclIsKindOf(OclAny))"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>  not(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .oclAsType(OclAny) .oclIsTypeOf(OclAny))"


Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .salary       \<doteq> \<one>\<eight>\<zero>\<zero>)"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .salary@pre   \<doteq> \<one>\<two>\<zero>\<zero>)"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .boss      \<doteq> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2)"
Assert "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .boss .salary@pre      \<doteq> \<one>\<two>\<zero>\<zero>)"
Assert "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .boss .boss@pre      \<doteq> null)"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .boss@pre  \<doteq> null)"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .boss@pre  <> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2)"
Assert "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .boss@pre  <> (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .boss))"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile> not(\<upsilon>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .boss@pre .boss))"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile> not(\<upsilon>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .boss@pre .salary@pre))"
lemma "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .oclIsMaintained())"
by(simp add: OclValid_def OclIsMaintained_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2_def person2_def
             oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def
             oid_of_option_def oid_of_type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)

Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 .salary       \<doteq> null)"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile> not(\<upsilon>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 .salary@pre))"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 .boss       \<doteq> null)"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile> not(\<upsilon>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 .boss .salary))"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile> not(\<upsilon>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 .boss@pre))"
lemma "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 .oclIsNew())"
by(simp add: OclValid_def OclIsNew_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3_def person3_def
             oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid8_def
             oid_of_option_def oid_of_type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)


Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 .boss@pre   \<doteq> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5)"
Assert "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile> not(\<upsilon>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 .boss@pre .salary))"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 .boss@pre .salary@pre   \<doteq> \<three>\<five>\<zero>\<zero>)"
lemma "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 .oclIsMaintained())"
by(simp add: OclValid_def OclIsMaintained_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4_def person4_def
             oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def
             oid_of_option_def oid_of_type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)

Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile> not(\<upsilon>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 .salary))"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 .salary@pre   \<doteq> \<three>\<five>\<zero>\<zero>)"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile> not(\<upsilon>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 .boss))"
lemma "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 .oclIsDeleted())"
by(simp add: OclNot_def OclValid_def OclIsDeleted_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5_def person5_def
             oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def
             oid_of_option_def oid_of_type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)

(* (* access to an oclany object not yet supported *) Assert "  (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>     ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 .boss .salary)   \<doteq> \<three>\<two>\<zero>\<zero> )"*)
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e     .   (s\<^sub>p\<^sub>r\<^sub>e,\<sigma>\<^sub>1') \<Turnstile> not(\<upsilon>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 .boss .salary@pre))"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 .boss@pre   \<doteq> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4)"
Assert "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 .boss@pre .salary   \<doteq> \<two>\<nine>\<zero>\<zero>)"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 .boss@pre .salary@pre   \<doteq> \<two>\<six>\<zero>\<zero>)"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 .boss@pre .boss@pre  \<doteq> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5)"
lemma "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 .oclIsMaintained())"
by(simp add: OclValid_def OclIsMaintained_def \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6_def person6_def
             oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def
             oid_of_option_def oid_of_type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def)

(* (* access to an oclany object not yet supported *) Assert "  (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>     ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .oclAsType(Person)   \<doteq>  (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 .boss)))" *)
(* (* access to an oclany object not yet supported *) Assert "  (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>     ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .oclAsType(Person) .boss)   \<doteq> (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .oclAsType(Person)) )" *)
(* (* access to an oclany object not yet supported *) Assert "  (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>     ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .oclAsType(Person) .boss .salary)   \<doteq> \<three>\<two>\<zero>\<zero> )" *)
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>     \<upsilon>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .oclAsType(Person))"
Assert "\<And>    s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.    (\<sigma>\<^sub>1,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile> not(\<upsilon>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .oclAsType(Person) .boss@pre))"
lemma "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>     ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .oclAsType(Person) .oclAsType(OclAny)
                                                                   .oclAsType(Person))
                                      \<doteq> (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .oclAsType(Person)))"
by(rule up_down_cast_Person_OclAny_Person', simp add: X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7_def OclValid_def valid_def person7_def)
lemma "               (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile>       (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .oclIsNew())"
by(simp add: OclValid_def OclIsNew_def  \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def  X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7_def person7_def
             oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid8_def
             oid_of_option_def oid_of_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def)

Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8  <> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7)"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile> not(\<upsilon>(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 .oclAsType(Person)))"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 .oclIsTypeOf(OclAny))"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>   not(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 .oclIsTypeOf(Person))"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>   not(X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 .oclIsKindOf(Person))"
Assert "\<And>s\<^sub>p\<^sub>r\<^sub>e s\<^sub>p\<^sub>o\<^sub>s\<^sub>t.   (s\<^sub>p\<^sub>r\<^sub>e,s\<^sub>p\<^sub>o\<^sub>s\<^sub>t) \<Turnstile>      (X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 .oclIsKindOf(OclAny))"

lemma \<sigma>_modifiedonly: "(\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile> (Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .oclAsType(OclAny)
                      , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .oclAsType(OclAny)
                      \<^cancel>\<open>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 .oclAsType(OclAny)\<close>
                      , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 .oclAsType(OclAny)
                      \<^cancel>\<open>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 .oclAsType(OclAny)\<close>
                      , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 .oclAsType(OclAny)
                      \<^cancel>\<open>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .oclAsType(OclAny)\<close>
                      \<^cancel>\<open>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 .oclAsType(OclAny)\<close>
                      \<^cancel>\<open>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 .oclAsType(OclAny)\<close>}->oclIsModifiedOnly())"
 apply(simp add: OclIsModifiedOnly_def OclValid_def
                 oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def
                 X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4_def
                 X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9_def
                 person1_def person2_def person3_def person4_def
                 person5_def person6_def person7_def person8_def person9_def
                 image_def)
 apply(simp add: OclIncluding_rep_set mtSet_rep_set null_option_def bot_option_def)
 apply(simp add: oid_of_option_def oid_of_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def, clarsimp)
 apply(simp add: \<sigma>\<^sub>1_def \<sigma>\<^sub>1'_def
                 oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def)
done

lemma "(\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile> ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 @pre (\<lambda>x. \<lfloor>OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> x\<rfloor>))  \<triangleq> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9)"
by(simp add: OclSelf_at_pre_def \<sigma>\<^sub>1_def oid_of_option_def oid_of_type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def
             X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9_def person9_def oid8_def OclValid_def StrongEq_def OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def)

lemma "(\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile> ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 @post (\<lambda>x. \<lfloor>OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA> x\<rfloor>))  \<triangleq> X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9)"
by(simp add: OclSelf_at_post_def \<sigma>\<^sub>1'_def oid_of_option_def oid_of_type\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_def
             X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9_def person9_def oid8_def OclValid_def StrongEq_def OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def)

lemma "(\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile> (((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 .oclAsType(OclAny)) @pre (\<lambda>x. \<lfloor>OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> x\<rfloor>)) \<triangleq>
                   ((X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 .oclAsType(OclAny)) @post (\<lambda>x. \<lfloor>OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA> x\<rfloor>)))"
proof -

 have including4 : "\<And>a b c d \<tau>.
        Set{\<lambda>\<tau>. \<lfloor>\<lfloor>a\<rfloor>\<rfloor>, \<lambda>\<tau>. \<lfloor>\<lfloor>b\<rfloor>\<rfloor>, \<lambda>\<tau>. \<lfloor>\<lfloor>c\<rfloor>\<rfloor>, \<lambda>\<tau>. \<lfloor>\<lfloor>d\<rfloor>\<rfloor>} \<tau> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> {\<lfloor>\<lfloor>a\<rfloor>\<rfloor>, \<lfloor>\<lfloor>b\<rfloor>\<rfloor>, \<lfloor>\<lfloor>c\<rfloor>\<rfloor>, \<lfloor>\<lfloor>d\<rfloor>\<rfloor>} \<rfloor>\<rfloor>"
  apply(subst abs_rep_simp'[symmetric], simp)
  apply(simp add: OclIncluding_rep_set mtSet_rep_set)
  by(rule arg_cong[of _ _ "\<lambda>x. (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e(\<lfloor>\<lfloor> x \<rfloor>\<rfloor>))"], auto)

 have excluding1: "\<And>S a b c d e \<tau>.
                   (\<lambda>_. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> {\<lfloor>\<lfloor>a\<rfloor>\<rfloor>, \<lfloor>\<lfloor>b\<rfloor>\<rfloor>, \<lfloor>\<lfloor>c\<rfloor>\<rfloor>, \<lfloor>\<lfloor>d\<rfloor>\<rfloor>} \<rfloor>\<rfloor>)->excluding\<^sub>S\<^sub>e\<^sub>t(\<lambda>\<tau>. \<lfloor>\<lfloor>e\<rfloor>\<rfloor>) \<tau> =
                   Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> {\<lfloor>\<lfloor>a\<rfloor>\<rfloor>, \<lfloor>\<lfloor>b\<rfloor>\<rfloor>, \<lfloor>\<lfloor>c\<rfloor>\<rfloor>, \<lfloor>\<lfloor>d\<rfloor>\<rfloor>} - {\<lfloor>\<lfloor>e\<rfloor>\<rfloor>} \<rfloor>\<rfloor>"
  apply(simp add: UML_Set.OclExcluding_def)
  apply(simp add: defined_def OclValid_def false_def true_def
                  bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
  apply(rule conjI)
   apply(rule impI, subst (asm) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject) apply( simp add: bot_option_def)+
  apply(rule conjI)
   apply(rule impI, subst (asm) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject) apply( simp add: bot_option_def null_option_def)+
  apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def, simp)
 done

 show ?thesis
  apply(rule framing[where X = "Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .oclAsType(OclAny)
                       , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .oclAsType(OclAny)
                       \<^cancel>\<open>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 .oclAsType(OclAny)\<close>
                       , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 .oclAsType(OclAny)
                       \<^cancel>\<open>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 .oclAsType(OclAny)\<close>
                       , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 .oclAsType(OclAny)
                       \<^cancel>\<open>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .oclAsType(OclAny)\<close>
                       \<^cancel>\<open>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 .oclAsType(OclAny)\<close>
                       \<^cancel>\<open>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 .oclAsType(OclAny)\<close>}"])
   apply(cut_tac \<sigma>_modifiedonly)
   apply(simp only: OclValid_def
                    X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4_def
                    X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9_def
                    person1_def person2_def person3_def person4_def
                    person5_def person6_def person7_def person8_def person9_def
                    OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_Person)
   apply(subst cp_OclIsModifiedOnly, subst UML_Set.OclExcluding.cp0,
     subst (asm) cp_OclIsModifiedOnly, simp add: including4 excluding1)

  apply(simp only: X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4_def
                   X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9_def
                   person1_def person2_def person3_def person4_def
                   person5_def person6_def person7_def person8_def person9_def)
  apply(simp add: OclIncluding_rep_set mtSet_rep_set
                  oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def)
  apply(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def oid_of_option_def oid_of_type\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_def OclNot_def OclValid_def
                  null_option_def bot_option_def)
 done
qed

lemma perm_\<sigma>\<^sub>1' : "\<sigma>\<^sub>1' = \<lparr> heap = Map.empty
                           (oid8 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person9)
                           (oid7 \<mapsto> in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y person8)
                           (oid6 \<mapsto> in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y person7)
                           (oid5 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person6)
                           \<^cancel>\<open>oid4\<close>
                           (oid3 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person4)
                           (oid2 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person3)
                           (oid1 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person2)
                           (oid0 \<mapsto> in\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n person1)
                       , assocs = assocs \<sigma>\<^sub>1' \<rparr>"
proof -
 note P = fun_upd_twist
 show ?thesis
  apply(simp add: \<sigma>\<^sub>1'_def
                  oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def)
  apply(subst (1) P, simp)
  apply(subst (2) P, simp) apply(subst (1) P, simp)
  apply(subst (3) P, simp) apply(subst (2) P, simp) apply(subst (1) P, simp)
  apply(subst (4) P, simp) apply(subst (3) P, simp) apply(subst (2) P, simp) apply(subst (1) P, simp)
  apply(subst (5) P, simp) apply(subst (4) P, simp) apply(subst (3) P, simp) apply(subst (2) P, simp) apply(subst (1) P, simp)
  apply(subst (6) P, simp) apply(subst (5) P, simp) apply(subst (4) P, simp) apply(subst (3) P, simp) apply(subst (2) P, simp) apply(subst (1) P, simp)
  apply(subst (7) P, simp) apply(subst (6) P, simp) apply(subst (5) P, simp) apply(subst (4) P, simp) apply(subst (3) P, simp) apply(subst (2) P, simp) apply(subst (1) P, simp)
 by(simp)
qed

declare const_ss [simp]

lemma "\<And>\<sigma>\<^sub>1.
 (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile> (Person .allInstances() \<doteq> Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4\<^cancel>\<open>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<close>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6,
                                           X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 .oclAsType(Person)\<^cancel>\<open>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8\<close>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 })"
 apply(subst perm_\<sigma>\<^sub>1')
 apply(simp only: oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def
                  X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4_def
                  X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9_def
                  person7_def)
 apply(subst state_update_vs_allInstances_at_post_tc, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
  apply(subst state_update_vs_allInstances_at_post_tc, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
   apply(subst state_update_vs_allInstances_at_post_tc, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
    apply(subst state_update_vs_allInstances_at_post_tc, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
     apply(subst state_update_vs_allInstances_at_post_tc, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
      apply(subst state_update_vs_allInstances_at_post_tc, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
       apply(subst state_update_vs_allInstances_at_post_ntc, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def
                                                                             person8_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp)
       apply(subst state_update_vs_allInstances_at_post_tc, simp, simp add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)
        apply(rule state_update_vs_allInstances_at_post_empty)
by(simp_all add: OclAsType\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n_\<AA>_def)

lemma "\<And>\<sigma>\<^sub>1.
 (\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<Turnstile> (OclAny .allInstances() \<doteq> Set{ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 .oclAsType(OclAny), X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 .oclAsType(OclAny),
                                           X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 .oclAsType(OclAny), X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 .oclAsType(OclAny)
                                           \<^cancel>\<open>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5\<close>, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 .oclAsType(OclAny),
                                           X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8, X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 .oclAsType(OclAny) })"
 apply(subst perm_\<sigma>\<^sub>1')
 apply(simp only: oid0_def oid1_def oid2_def oid3_def oid4_def oid5_def oid6_def oid7_def oid8_def
                  X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8_def X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9_def
                  person1_def person2_def person3_def person4_def person5_def person6_def person9_def)
 apply(subst state_update_vs_allInstances_at_post_tc, simp, simp add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def, simp, rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including, simp, simp, simp, rule OclIncluding_cong, simp, simp)+
         apply(rule state_update_vs_allInstances_at_post_empty)
by(simp_all add: OclAsType\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y_\<AA>_def)

end
