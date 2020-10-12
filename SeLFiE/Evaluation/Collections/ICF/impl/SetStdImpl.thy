(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section "Standard Set Implementations"
theory SetStdImpl
imports 
  ListSetImpl 
  ListSetImpl_Invar 
  ListSetImpl_NotDist
  ListSetImpl_Sorted
  RBTSetImpl HashSet 
  TrieSetImpl 
  ArrayHashSet
  ArraySetImpl
begin
text_raw \<open>\label{thy:SetStdImpl}\<close>
text \<open>
  This theory summarizes standard set implementations, namely list-sets RB-tree-sets, trie-sets and hashsets.
\<close>

end
