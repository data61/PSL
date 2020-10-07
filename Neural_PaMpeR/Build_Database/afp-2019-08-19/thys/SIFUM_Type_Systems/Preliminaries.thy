(*
Title: SIFUM-Type-Systems
Authors: Sylvia Grewe, Heiko Mantel, Daniel Schoepe
*)
section \<open>Preliminaries\<close>
theory Preliminaries
imports Main "HOL-Library.Lattice_Syntax"
begin

text \<open>Possible modes for variables:\<close>
datatype Mode = AsmNoRead | AsmNoWrite | GuarNoRead | GuarNoWrite

text \<open>We consider a two-element security lattice:\<close>
datatype Sec = High | Low

notation
  less_eq  (infix "\<sqsubseteq>" 50) and
  less  (infix "\<sqsubset>" 50)

text \<open>@{term Sec} forms a (complete) lattice:\<close>
instantiation Sec :: complete_lattice
begin

definition top_Sec_def: "\<top> = High"
definition sup_Sec_def: "d1 \<squnion> d2 = (if (d1 = High \<or> d2 = High) then High else Low)"
definition inf_Sec_def: "d1 \<sqinter> d2 = (if (d1 = Low \<or> d2 = Low) then Low else High)"
definition bot_Sec_def: "\<bottom> = Low"
definition less_eq_Sec_def: "d1 \<le> d2 = (d1 = d2 \<or> d1 = Low)"
definition less_Sec_def: "d1 < d2 = (d1 = Low \<and> d2 = High)"
definition Sup_Sec_def: "\<Squnion>S = (if (High \<in> S) then High else Low)"
definition Inf_Sec_def: "\<Sqinter>S = (if (Low \<in> S) then Low else High)"

instance
  apply (intro_classes)
  apply (metis Sec.exhaust Sec.simps(2) less_Sec_def less_eq_Sec_def)
  apply (metis less_eq_Sec_def)
  apply (metis less_eq_Sec_def)
  apply (metis less_eq_Sec_def)
  apply (metis Sec.exhaust inf_Sec_def less_eq_Sec_def)
  apply (metis Sec.exhaust inf_Sec_def less_eq_Sec_def)
  apply (metis Sec.exhaust inf_Sec_def less_eq_Sec_def)
  apply (metis Sec.exhaust less_eq_Sec_def sup_Sec_def)
  apply (metis Sec.exhaust less_eq_Sec_def sup_Sec_def)
  apply (metis Sec.exhaust Sec.simps(2) less_eq_Sec_def sup_Sec_def)
  apply (metis (full_types) Inf_Sec_def Sec.exhaust less_eq_Sec_def)
  apply (metis Inf_Sec_def Sec.exhaust less_eq_Sec_def)
  apply (metis Sec.exhaust Sup_Sec_def less_eq_Sec_def)
  apply (metis (full_types) Sup_Sec_def less_eq_Sec_def)
  apply (metis (hide_lams, mono_tags) Inf_Sec_def empty_iff top_Sec_def)
  by (metis (hide_lams, mono_tags) Sup_Sec_def bot_Sec_def empty_iff)
end

text \<open>Memories are mappings from variables to values\<close>
type_synonym ('var, 'val) Mem = "'var \<Rightarrow> 'val"

text \<open>A mode state maps modes to the set of variables for which the
  given mode is set.\<close>
type_synonym 'var Mds = "Mode \<Rightarrow> 'var set"

text \<open>Local configurations:\<close>
type_synonym ('com, 'var, 'val) LocalConf = "('com \<times> 'var Mds) \<times> ('var, 'val) Mem"

text \<open>Global configurations:\<close>
type_synonym ('com, 'var, 'val) GlobalConf = "('com \<times> 'var Mds) list \<times> ('var, 'val) Mem"

text \<open>A locale to fix various parametric components in Mantel et. al, and assumptions
  about them:\<close>
locale sifum_security =
  fixes dma :: "'Var \<Rightarrow> Sec"
  fixes stop :: "'Com"
  fixes eval :: "('Com, 'Var, 'Val) LocalConf rel"
  fixes some_val :: "'Val"
  fixes some_val' :: "'Val"
  assumes stop_no_eval: "\<not> ((((stop, mds), mem), ((c', mds'), mem')) \<in> eval)"
  assumes deterministic: "\<lbrakk> (lc, lc') \<in> eval; (lc, lc'') \<in> eval \<rbrakk> \<Longrightarrow> lc' = lc''"
  assumes finite_memory: "finite {(x::'Var). True}"
  assumes different_values: "some_val \<noteq> some_val'"

end
