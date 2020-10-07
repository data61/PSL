(*  Title:      Native_Word_Imperative_HOL.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

section \<open>Compatibility with Imperative/HOL\<close>

theory Native_Word_Imperative_HOL imports
  Code_Target_Word_Base
  "HOL-Imperative_HOL.Heap_Monad"
begin

text \<open>
  We add a code target that combines the translations for native words that are by default not
  supported by all PolyML versions with the adaptations for Imperative\_HOL.
\<close>

setup \<open>Code_Target.add_derived_target ("SML_word_imp", [("SML_word", I), ("SML_imp", I)])\<close>

end
