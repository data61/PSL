(*
Title: Value-Dependent SIFUM-Type-Systems
Authors: Toby Murray, Robert Sison, Edward Pierzchalski, Christine Rizkallah
(Based on the SIFUM-Type-Systems AFP entry, whose authors
 are: Sylvia Grewe, Heiko Mantel, Daniel Schoepe)
*)
section \<open>Preliminaries\<close>
theory Preliminaries
imports Main (* "HOL-Library.Lattice_Syntax" *)
begin

text \<open>Possible modes for variables:\<close>
datatype Mode = AsmNoReadOrWrite | AsmNoWrite | GuarNoReadOrWrite | GuarNoWrite

text \<open>We consider a two-element security lattice:\<close>
datatype Sec = High | Low


text \<open>@{term Sec} forms a (complete) lattice:\<close>
instantiation Sec :: complete_lattice
begin

definition top_Sec_def: "top = High"
definition sup_Sec_def: "sup d1 d2 = (if (d1 = High \<or> d2 = High) then High else Low)"
definition inf_Sec_def: "inf d1 d2 = (if (d1 = Low \<or> d2 = Low) then Low else High)"
definition bot_Sec_def: "bot = Low"
definition less_eq_Sec_def: "d1 \<le> d2 = (d1 = d2 \<or> d1 = Low)"
definition less_Sec_def: "d1 < d2 = (d1 = Low \<and> d2 = High)"
definition Sup_Sec_def: "Sup S = (if (High \<in> S) then High else Low)"
definition Inf_Sec_def: "Inf S = (if (Low \<in> S) then Low else High)"

instance
  apply (intro_classes)
                 using Sec.exhaust less_Sec_def less_eq_Sec_def inf_Sec_def sup_Sec_def apply auto[10]
       apply (metis Inf_Sec_def Sec.exhaust less_eq_Sec_def)
      apply (metis Inf_Sec_def Sec.exhaust less_eq_Sec_def)
     using Sec.exhaust less_Sec_def less_eq_Sec_def inf_Sec_def sup_Sec_def Inf_Sec_def Sup_Sec_def top_Sec_def bot_Sec_def 
     by auto
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
locale sifum_security_init =
  fixes dma :: "('Var,'Val) Mem \<Rightarrow> 'Var \<Rightarrow> Sec"
  fixes \<C>_vars :: "'Var \<Rightarrow> 'Var set"
  fixes \<C> :: "'Var set" (* classification control variables *)
  fixes eval :: "('Com, 'Var, 'Val) LocalConf rel"
  fixes some_val :: "'Val"
  fixes INIT :: "('Var,'Val) Mem \<Rightarrow> bool"
  assumes deterministic: "\<lbrakk> (lc, lc') \<in> eval; (lc, lc'') \<in> eval \<rbrakk> \<Longrightarrow> lc' = lc''"
  assumes finite_memory: "finite {(x::'Var). True}"
  defines "\<C> \<equiv> \<Union>x. \<C>_vars x"
  assumes \<C>_vars_\<C>: "x \<in> \<C> \<Longrightarrow> \<C>_vars x = {}"
  assumes dma_\<C>_vars: "\<forall>x\<in>\<C>_vars y. mem\<^sub>1 x = mem\<^sub>2 x \<Longrightarrow> dma mem\<^sub>1 y = dma mem\<^sub>2 y"
  assumes \<C>_Low: "\<forall>x\<in>\<C>. dma mem x = Low"

locale sifum_security = sifum_security_init dma \<C>_vars \<C> eval some_val "\<lambda>_.True"
  for dma :: "('Var,'Val) Mem \<Rightarrow> 'Var \<Rightarrow> Sec"
  and \<C>_vars :: "'Var \<Rightarrow> 'Var set"
  and \<C> :: "'Var set" (* classification control variables *)
  and eval :: "('Com, 'Var, 'Val) LocalConf rel"
  and some_val :: "'Val"

context sifum_security_init begin

lemma \<C>_vars_subset_\<C>:
  "\<C>_vars x \<subseteq> \<C>"
  by(force simp: \<C>_def)

lemma dma_\<C>:
  "\<forall>x\<in>\<C>. mem\<^sub>1 x = mem\<^sub>2 x \<Longrightarrow> dma mem\<^sub>1 = dma mem\<^sub>2"
  proof
    fix y
    assume "\<forall>x\<in>\<C>. mem\<^sub>1 x = mem\<^sub>2 x"
    hence "\<forall>x\<in>\<C>_vars y. mem\<^sub>1 x = mem\<^sub>2 x"
      using \<C>_vars_subset_\<C> by blast
    thus "dma mem\<^sub>1 y = dma mem\<^sub>2 y"
      by(rule dma_\<C>_vars)
  qed

end

(* induction tools, moved up as far as possible *)

lemma my_trancl_induct [consumes 1, case_names base step]:
  "\<lbrakk>(a, b) \<in> r\<^sup>+; 
    P a ; 
   \<And>x y. \<lbrakk>(x, y) \<in> r; P x\<rbrakk> \<Longrightarrow> P y\<rbrakk> \<Longrightarrow> P b"
  by (induct rule: trancl.induct, blast+)
  
lemma my_trancl_step_induct [consumes 1, case_names base step]:
  "\<lbrakk>(a, b) \<in> r\<^sup>+; 
   \<And>x y. (x, y) \<in> r \<Longrightarrow> P x y;
   \<And>x y z. P x y \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> P x z\<rbrakk> \<Longrightarrow> P a b"
  by (induct rule: trancl_induct, blast+)
  
lemma my_trancl_big_step_induct [consumes 1, case_names base step]:
  "\<lbrakk>(a, b) \<in> r\<^sup>+; 
   \<And>x y. (x, y) \<in> r \<Longrightarrow> P x y;
   \<And>x y z. (x, y) \<in> r\<^sup>+ \<Longrightarrow> P x y \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> P y z \<Longrightarrow> P x z\<rbrakk> \<Longrightarrow> P a b"
  by (induct rule: trancl.induct, blast+)
  
lemmas my_trancl_step_induct3 = 
  my_trancl_step_induct[of "((ax,ay), az)" "((bx,by), bz)", split_format (complete),
                 consumes 1, case_names step]
  
lemmas my_trancl_big_step_induct3 = 
  my_trancl_big_step_induct[of "((ax,ay), az)" "((bx,by), bz)", split_format (complete),
                 consumes 1, case_names base step]

end
