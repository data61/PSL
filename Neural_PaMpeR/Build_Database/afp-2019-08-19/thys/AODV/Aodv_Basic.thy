(*  Title:       Aodv_Basic.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
*)

section "Basic data types and constants"

theory Aodv_Basic
imports Main AWN.AWN_SOS
begin

text \<open>These definitions are shared with all variants.\<close>

type_synonym rreqid = nat
type_synonym sqn = nat

datatype k = Known | Unknown
abbreviation kno where "kno \<equiv> Known"
abbreviation unk where "unk \<equiv> Unknown"

datatype p = NoRequestRequired | RequestRequired
abbreviation noreq where "noreq \<equiv> NoRequestRequired"
abbreviation req where "req \<equiv> RequestRequired"

datatype f = Valid | Invalid
abbreviation val where "val \<equiv> Valid"
abbreviation inv where "inv \<equiv> Invalid"

lemma not_ks [simp]:                                      
   "(x \<noteq> kno) = (x = unk)"
   "(x \<noteq> unk) = (x = kno)"
  by (cases x, clarsimp+)+

lemma not_ps [simp]:
  "(x \<noteq> noreq) = (x = req)"
  "(x \<noteq> req) = (x = noreq)"
  by (cases x, clarsimp+)+

lemma not_ffs [simp]:
  "(x \<noteq> val) = (x = inv)"
  "(x \<noteq> inv) = (x = val)"
  by (cases x, clarsimp+)+

end
