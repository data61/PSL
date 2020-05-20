(* Title:    Error_Syntax  
   Author:   Christian Sternagel
*)

section \<open>Try-Catch and Error-Update Notation for Arbitrary Types\<close>

theory Error_Syntax
imports
  Main
  "HOL-Library.Adhoc_Overloading"
begin

consts
  catch :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c" ("(try(/ _)/ catch(/ _))" [12, 12] 13)
  update_error :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'd" (infixl "<+?" 61)

syntax
  "_replace_error" :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" (infixl "<?" 61)

translations
  "m <? e" \<rightharpoonup> "m <+? (\<lambda>_. e)"

end

