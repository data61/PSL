(* Title:      Examples using Hoare Logic for Total Correctness
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Examples using Hoare Logic for Total Correctness\<close>

theory Hoare_Logic_Examples

imports Hoare_Logic

begin

text \<open>
This theory demonstrates a few simple partial- and total-correctness proofs.
The first example is taken from HOL/Hoare/Examples.thy written by N. Galm.
We have added the invariant $m \leq a$.
\<close>

lemma multiply_by_add: "VARS m s a b
  {a=A \<and> b=B}
  m := 0; s := 0;
  WHILE m\<noteq>a
  INV {s=m*b \<and> a=A \<and> b=B \<and> m\<le>a}
  DO s := s+b; m := m+(1::nat) OD
  {s = A*B}"
  by vcg_simp

text \<open>
Here is the total-correctness proof for the same program.
It needs the additional invariant $m \leq a$.
\<close>

lemma multiply_by_add_tc: "VARS m s a b
  [a=A \<and> b=B]
  m := 0; s := 0;
  WHILE m\<noteq>a
  INV {s=m*b \<and> a=A \<and> b=B \<and> m\<le>a}
  VAR {a-m}
  DO s := s+b; m := m+(1::nat) OD
  [s = A*B]"
  apply vcg_tc_simp
  by auto

text \<open>
Next, we prove partial correctness of a program that computes powers.
\<close>

lemma power: "VARS (x::nat) n p i
  { 0 \<le> n }
  p := 1;
  i := 0;
  WHILE i < n
    INV { p = x^i \<and> i \<le> n }
     DO p := p * x;
        i := i + 1
     OD
  { p = x^n }"
  apply vcg_simp
  by auto

text \<open>
Here is its total-correctness proof.
\<close>

lemma power_tc: "VARS (x::nat) n p i
  [ 0 \<le> n ]
  p := 1;
  i := 0;
  WHILE i < n
    INV { p = x^i \<and> i \<le> n }
    VAR { n - i }
     DO p := p * x;
        i := i + 1
     OD
  [ p = x^n ]"
  apply vcg_tc
  by auto

end
