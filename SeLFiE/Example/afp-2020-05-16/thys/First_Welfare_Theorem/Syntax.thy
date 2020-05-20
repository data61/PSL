(* License: LGPL *)
(*
Author: Julian Parsert <julian.parsert@gmail.com>
Author: Cezary Kaliszyk
*)

section \<open> Introducing Syntax \<close>

text \<open> Syntax, abbreviations and type-synonyms \<close>

theory Syntax
  imports Main
begin


type_synonym 'a relation = "('a \<times> 'a) set"

abbreviation gen_weak_stx :: "'a \<Rightarrow> 'a relation \<Rightarrow> 'a \<Rightarrow> bool"
  ("_ \<succeq>[_] _" [51,100,51] 60)
  where
    "x \<succeq>[P] y \<equiv> (x, y) \<in> P"

abbreviation gen_indif_stx :: "'a \<Rightarrow> 'a relation \<Rightarrow> 'a \<Rightarrow> bool"
  ("_ \<approx>[_] _" [51,100,51] 60)
  where
    "x \<approx>[P] y \<equiv> x \<succeq>[P] y \<and> y \<succeq>[P] x "

abbreviation gen_strc_stx :: "'a \<Rightarrow> 'a relation \<Rightarrow> 'a \<Rightarrow> bool"
  ("_ \<succ>[_] _" [51,100,51] 60)
  where
    "x \<succ>[P] y \<equiv>  x \<succeq>[P] y \<and> \<not>y \<succeq>[P] x "


end
