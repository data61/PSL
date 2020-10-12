(*
    Author:   Salomon Sickert
    License:  BSD
*)

section \<open>Example\<close>

theory Example
imports
  "../LTL" "../Rewriting" "HOL-Library.Code_Target_Numeral"
begin

\<comment> \<open>The included parser always returns a @{typ "String.literal ltlc"}. If a different labelling
  is needed one can use @{const map_ltlc} to relabel the leafs. In our example we prepend a
  string to each atom.\<close>

definition rewrite :: "String.literal ltlc \<Rightarrow> String.literal ltlc"
where
  "rewrite \<equiv> ltln_to_ltlc o rewrite_iter_slow o ltlc_to_ltln o (map_ltlc (\<lambda>s. String.implode ''prop('' + s + String.implode '')''))"

\<comment> \<open>Export rewriting engine (and also constructors)\<close>

export_code true\<^sub>c Iff_ltlc rewrite in SML file_prefix \<open>rewrite_example\<close>

end
