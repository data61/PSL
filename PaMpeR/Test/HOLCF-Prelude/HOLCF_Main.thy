section \<open>Initial Setup for HOLCF-Prelude\<close>

theory HOLCF_Main
  imports
    HOLCF
    "HOLCF-Library.Int_Discrete"
begin

text \<open>
  All theories from the Isabelle distribution which are used
  anywhere in the HOLCF-Prelude library must be imported via this file.
  This way, we only have to hide constant names and syntax in one place.
\<close>

hide_type (open) list

hide_const (open)
  List.append List.concat List.Cons List.distinct List.filter List.last
  List.foldr List.foldl List.length List.lists List.map List.Nil List.nth
  List.partition List.replicate List.set List.take List.upto List.zip
  Orderings.less Product_Type.fst Product_Type.snd

no_notation Map.map_add (infixl "++" 100)

no_notation List.upto ("(1[_../_])")

no_notation
  Rings.divide (infixl "div" 70) and
  Rings.modulo (infixl "mod" 70)

no_notation
  Set.member  ("op :") and
  Set.member  ("(_/ : _)" [51, 51] 50)

no_translations
  "[x, xs]" == "x # [xs]"
  "[x]" == "x # []"

no_syntax
  "_list" :: "args \<Rightarrow> 'a List.list"    ("[(_)]")

no_notation
  List.Nil ("[]")

no_syntax "_bracket" :: "types \<Rightarrow> type \<Rightarrow> type" ("([_]/ => _)" [0, 0] 0)
no_syntax "_bracket" :: "types \<Rightarrow> type \<Rightarrow> type" ("([_]/ \<Rightarrow> _)" [0, 0] 0)

no_translations
  "[x<-xs . P]" == "CONST List.filter (%x. P) xs"

no_syntax (ASCII)
  "_filter" :: "pttrn \<Rightarrow> 'a List.list \<Rightarrow> bool \<Rightarrow> 'a List.list" ("(1[_<-_./ _])")

no_syntax
  "_filter" :: "pttrn \<Rightarrow> 'a List.list \<Rightarrow> bool \<Rightarrow> 'a List.list" ("(1[_\<leftarrow>_ ./ _])")

text \<open>Declarations that belong in HOLCF/Tr.thy:\<close>

declare trE [cases type: tr]
declare tr_induct [induct type: tr]

end
