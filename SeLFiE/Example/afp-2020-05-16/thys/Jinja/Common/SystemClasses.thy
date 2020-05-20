(*  Title:      HOL/MicroJava/J/SystemClasses.thy

    Author:     Gerwin Klein
    Copyright   2002 Technische Universitaet Muenchen
*)

section \<open>System Classes\<close>

theory SystemClasses
imports Decl Exceptions
begin

text \<open>
  This theory provides definitions for the \<open>Object\<close> class,
  and the system exceptions.
\<close>

definition ObjectC :: "'m cdecl"
where
  "ObjectC \<equiv> (Object, (undefined,[],[]))"

definition NullPointerC :: "'m cdecl"
where
  "NullPointerC \<equiv> (NullPointer, (Object,[],[]))"

definition ClassCastC :: "'m cdecl"
where
  "ClassCastC \<equiv> (ClassCast, (Object,[],[]))"

definition OutOfMemoryC :: "'m cdecl"
where
  "OutOfMemoryC \<equiv> (OutOfMemory, (Object,[],[]))"

definition SystemClasses :: "'m cdecl list"
where
  "SystemClasses \<equiv> [ObjectC, NullPointerC, ClassCastC, OutOfMemoryC]"

end
