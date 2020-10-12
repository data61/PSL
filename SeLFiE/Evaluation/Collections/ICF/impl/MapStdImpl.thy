(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section "Standard Implementations of Maps"
theory MapStdImpl
imports 
  ListMapImpl 
  ListMapImpl_Invar 
  RBTMapImpl 
  HashMap 
  TrieMapImpl 
  ArrayHashMap
  ArrayMapImpl
begin
text_raw \<open>\label{thy:MapStdImpl}\<close>
text \<open>
  This theory summarizes various standard implementation of maps, namely list-maps, RB-tree-maps, trie-maps, hashmaps, indexed array maps.
\<close>
end
