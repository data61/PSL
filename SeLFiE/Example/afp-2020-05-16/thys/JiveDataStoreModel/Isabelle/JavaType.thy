(*  Title:       Jive Data and Store Model
    Author:      Norbert Schirmer <schirmer at informatik.tu-muenchen.de>, 2003
    Maintainer:  Nicole Rauch <rauch at informatik.uni-kl.de>
    License:     LGPL
*)

section \<open>Java-Type\<close>
 
theory JavaType imports "../Isa_Counter/TypeIds"
begin

text \<open>This theory formalizes the types that appear in a Java program. Note that
the types defined by the classes and interfaces are formalized via their identifiers.
This way, this theory is program-independent.
\<close>

text \<open>We only want to formalize one-dimensional arrays. Therefore, we 
describe the types that can be used as element types of arrays. This excludes
the \texttt{null} type and array types themselves. This way, we get a finite 
number
of types in our type hierarchy, and the subtype relations can be given
explicitly (see Sec. \ref{direct_subtype_relations}). 
If desired, this can be extended in the future by using Javatype as argument
type of the \<open>ArrT\<close> type constructor. This will yield infinitely many
types.
\<close>

datatype Arraytype = BoolAT | IntgAT | ShortAT | ByteAT
                  | CClassAT CTypeId | AClassAT ATypeId
                  | InterfaceAT ITypeId

datatype Javatype = BoolT | IntgT | ShortT | ByteT | NullT | ArrT Arraytype
                  | CClassT CTypeId | AClassT ATypeId
                  | InterfaceT ITypeId

text \<open>We need a function that widens @{typ Arraytype} to @{typ Javatype}.
\<close>

definition
  at2jt :: "Arraytype \<Rightarrow> Javatype"
where
  "at2jt at = (case at of 
         BoolAT               \<Rightarrow> BoolT
       | IntgAT               \<Rightarrow> IntgT
       | ShortAT              \<Rightarrow> ShortT
       | ByteAT               \<Rightarrow> ByteT
       | CClassAT CTypeId     \<Rightarrow> CClassT CTypeId
       | AClassAT ATypeId     \<Rightarrow> AClassT ATypeId
       | InterfaceAT ITypeId  \<Rightarrow> InterfaceT ITypeId)"
  
text \<open>We define two predicates that separate the primitive types and the 
class types.
\<close>
                             
primrec isprimitive:: "Javatype \<Rightarrow> bool"
where
"isprimitive BoolT = True" |
"isprimitive IntgT = True" |
"isprimitive ShortT = True" |
"isprimitive ByteT = True" |
"isprimitive NullT = False" |
"isprimitive (ArrT T) = False" |
"isprimitive (CClassT c) = False" |
"isprimitive (AClassT c) = False" |
"isprimitive (InterfaceT i) = False" 

primrec isclass:: "Javatype \<Rightarrow> bool"
where
"isclass BoolT = False" |
"isclass IntgT = False" |
"isclass ShortT = False" |
"isclass ByteT = False" |
"isclass NullT = False" |
"isclass (ArrT T) = False" |
"isclass (CClassT c) = True" |
"isclass (AClassT c) = True" |
"isclass (InterfaceT i) = False" 

end
