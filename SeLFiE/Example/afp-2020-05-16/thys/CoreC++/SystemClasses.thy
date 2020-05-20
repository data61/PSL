(*  Title:       CoreC++
    Author:      Gerwin Klein
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)

section \<open>System Classes\<close>

theory SystemClasses imports Exceptions begin


text \<open>
  This theory provides definitions for the system exceptions.
\<close>

definition NullPointerC :: "cdecl" where
  "NullPointerC \<equiv> (NullPointer, ([],[],[]))"

definition ClassCastC :: "cdecl" where
  "ClassCastC \<equiv> (ClassCast, ([],[],[]))"

definition OutOfMemoryC :: "cdecl" where
  "OutOfMemoryC \<equiv> (OutOfMemory, ([],[],[]))"

definition SystemClasses :: "cdecl list" where
  "SystemClasses \<equiv> [NullPointerC, ClassCastC, OutOfMemoryC]"

end
