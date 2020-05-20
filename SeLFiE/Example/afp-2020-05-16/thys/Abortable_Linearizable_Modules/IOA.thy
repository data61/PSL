section \<open>I/O Automata with Finite-Trace Semantics\<close>

theory IOA
imports Main Sequences
begin

text \<open>This theory is inspired and draws material from the IOA theory of Nipkow and Müller\<close>

locale IOA = Sequences

record 'a signature =
  inputs::"'a set"
  outputs::"'a set"
  internals::"'a set"

context IOA
begin 

subsection \<open>Signatures\<close>

definition actions :: "'a signature \<Rightarrow> 'a set" where
  "actions asig \<equiv> inputs asig \<union> outputs asig \<union> internals asig"

definition externals :: "'a signature \<Rightarrow> 'a set" where
  "externals asig \<equiv> inputs asig \<union> outputs asig"

definition locals :: "'a signature \<Rightarrow> 'a set" where
  "locals asig \<equiv> internals asig \<union> outputs asig"

definition is_asig :: "'a signature \<Rightarrow> bool" where
  "is_asig triple \<equiv>
     inputs triple \<inter> outputs triple = {} \<and>
     outputs triple \<inter> internals triple = {} \<and>
     inputs triple \<inter> internals triple = {}"

lemma internal_inter_external:
  assumes "is_asig sig"
  shows "internals sig \<inter> externals sig = {}"
  using assms by (auto simp add:internals_def externals_def is_asig_def)

definition hide_asig where
  "hide_asig asig actns \<equiv>
    \<lparr>inputs = inputs asig - actns, outputs = outputs asig - actns, 
      internals = internals asig \<union>actns\<rparr>"

end

subsection \<open>I/O Automata\<close>

type_synonym
  ('s,'a) transition = "'s \<times> 'a \<times> 's"

record ('s,'a) ioa = 
  asig::"'a signature"
  start::"'s set"
  trans::"('s,'a)transition set"

context IOA 
begin

abbreviation "act A \<equiv> actions (asig A)"
abbreviation "ext A \<equiv> externals (asig A)"
abbreviation int where "int A \<equiv> internals (asig A)"
abbreviation "inp A \<equiv> inputs (asig A)"
abbreviation "out A \<equiv> outputs (asig A)"
abbreviation "local A \<equiv> locals (asig A)"

definition is_ioa::"('s,'a) ioa \<Rightarrow> bool" where
  "is_ioa A \<equiv> is_asig (asig A)
    \<and> (\<forall> triple  \<in> trans A . (fst o snd) triple \<in> act A)"

definition hide where
  "hide A actns \<equiv> A\<lparr>asig := hide_asig (asig A) actns\<rparr>"

definition is_trans::"'s \<Rightarrow> 'a \<Rightarrow> ('s,'a)ioa \<Rightarrow> 's \<Rightarrow> bool" where
  "is_trans s1 a A s2 \<equiv> (s1,a,s2) \<in> trans A"

notation
  is_trans  ("_ \<midarrow>_\<midarrow>_\<longrightarrow> _" [81,81,81,81] 100)

definition rename_set where
  "rename_set A ren \<equiv> {b. \<exists> x \<in> A . ren b = Some x}"

definition rename where
"rename A ren \<equiv>
  \<lparr>asig = \<lparr>inputs = rename_set (inp A) ren, 
    outputs = rename_set (out A) ren, 
    internals = rename_set (int A) ren\<rparr>,
   start = start A,
   trans = {tr. \<exists> x . ren (fst (snd tr)) = Some x \<and> (fst tr) \<midarrow>x\<midarrow>A\<longrightarrow> (snd (snd tr))}\<rparr>"

text \<open>Reachable states and invariants\<close>

inductive
  reachable :: "('s,'a) ioa \<Rightarrow> 's \<Rightarrow> bool"
  for A :: "('s,'a) ioa"
  where
    reachable_0:  "s \<in> start A \<Longrightarrow> reachable A s"
  | reachable_n:  "\<lbrakk> reachable A s; s \<midarrow>a\<midarrow>A\<longrightarrow> t \<rbrakk> \<Longrightarrow> reachable A t"

definition invariant where 
  "invariant A P \<equiv> (\<forall> s . reachable A s \<longrightarrow> P(s))"

theorem invariantI:
  fixes A P
  assumes "\<And> s . s \<in> start A \<Longrightarrow> P s"
  and "\<And> s t a . \<lbrakk>reachable A s; P s; s \<midarrow>a\<midarrow>A\<longrightarrow> t\<rbrakk> \<Longrightarrow> P t"
  shows "invariant A P"
proof -
  { fix s
    assume "reachable A s"
    hence "P s"
    proof (induct rule:reachable.induct)
      fix s
      assume "s \<in> start A"
      thus "P s" using assms(1) by simp
    next
      fix a s t
      assume "reachable A s" and "P s" and " s \<midarrow>a\<midarrow>A\<longrightarrow> t"
      thus "P t" using assms(2) by simp
    qed }
  thus ?thesis by (simp add:invariant_def)
qed

end

subsection \<open>Composition of Families of I/O Automata\<close>

record ('id, 'a) family =
  ids :: "'id set"
  memb :: "'id \<Rightarrow> 'a"

context IOA
begin

definition is_ioa_fam where
  "is_ioa_fam fam \<equiv> \<forall> i \<in> ids fam . is_ioa (memb fam i)"

definition compatible2  where
  "compatible2 A B \<equiv>
   out A \<inter> out B = {} \<and>
   int A \<inter> act B = {} \<and>
   int B \<inter> act A = {}"

definition compatible::"('id, ('s,'a)ioa) family \<Rightarrow> bool" where
  "compatible fam \<equiv> finite (ids fam) \<and>
    (\<forall> i \<in> ids fam . \<forall> j \<in> ids fam . i \<noteq> j \<longrightarrow>
      compatible2 (memb fam i) (memb fam j))"

definition asig_comp2 where
  "asig_comp2 A B \<equiv>
     \<lparr>inputs = (inputs A \<union> inputs B) - (outputs A \<union> outputs B),
      outputs = outputs A \<union> outputs B,
      internals = internals A \<union> internals B\<rparr>"
      
definition asig_comp::"('id, ('s,'a)ioa) family \<Rightarrow> 'a signature" where
  "asig_comp fam \<equiv> 
    \<lparr> inputs = \<Union>i\<in>(ids fam). inp (memb fam i) 
        - (\<Union>i\<in>(ids fam). out (memb fam i)),
      outputs = \<Union>i\<in>(ids fam). out (memb fam i),
      internals = \<Union>i\<in>(ids fam). int (memb fam i) \<rparr>"

definition par2 (infixr "\<parallel>" 10) where
  "A \<parallel> B \<equiv>
      \<lparr>asig = asig_comp2 (asig A) (asig B),
       start = {pr. fst pr \<in> start A \<and> snd pr \<in> start B},
       trans = {tr. 
        let s = fst tr; a = fst (snd tr); t = snd (snd tr)
        in (a \<in> act A \<or> a \<in> act B)
           \<and> (if a \<in> act A
              then fst s \<midarrow>a\<midarrow>A\<longrightarrow> fst t
              else fst s = fst t)
           \<and> (if a \<in> act B
              then snd s \<midarrow>a\<midarrow>B\<longrightarrow> snd t
              else snd s = snd t) }\<rparr>"
                
definition par::"('id, ('s,'a)ioa) family \<Rightarrow> ('id \<Rightarrow> 's,'a)ioa" where
  "par fam \<equiv> let ids = ids fam; memb = memb fam in
      \<lparr> asig = asig_comp fam,
        start = {s . \<forall> i\<in>ids . s i \<in> start (memb i)},
        trans = { (s, a, s') . 
          (\<exists> i\<in>ids . a \<in> act (memb i))
          \<and> (\<forall> i\<in>ids . 
              if a \<in> act (memb i)
              then s i \<midarrow>a\<midarrow>(memb i)\<longrightarrow> s' i
              else s i = (s' i)) } \<rparr>"

lemmas asig_simps = hide_asig_def is_asig_def locals_def externals_def actions_def 
  hide_def compatible_def asig_comp_def
lemmas ioa_simps = rename_def rename_set_def is_trans_def is_ioa_def par_def

end

subsection \<open>Executions and Traces\<close>

type_synonym
   ('s,'a)pairs = "('a\<times>'s) list"
type_synonym
   ('s,'a)execution = "'s \<times> ('s,'a)pairs"
type_synonym
   'a trace = "'a list"
   
record ('s,'a)execution_module =
  execs::"('s,'a)execution set"
  asig::"'a signature"
  
record 'a trace_module =
  traces::"'a trace set"
  asig::"'a signature"

context IOA
begin

fun is_exec_frag_of::"('s,'a)ioa \<Rightarrow> ('s,'a)execution \<Rightarrow> bool" where
  "is_exec_frag_of A (s,(ps#p')#p) = 
    (snd p' \<midarrow>fst p\<midarrow>A\<longrightarrow> snd p \<and> is_exec_frag_of A (s, (ps#p')))"
| "is_exec_frag_of A (s, [p]) = s \<midarrow>fst p\<midarrow>A\<longrightarrow> snd p"
| "is_exec_frag_of A (s, []) = True"

definition is_exec_of::"('s,'a)ioa \<Rightarrow> ('s,'a)execution \<Rightarrow> bool" where
  "is_exec_of A e \<equiv> fst e \<in> start A \<and> is_exec_frag_of A e"
  
definition filter_act where
  "filter_act \<equiv> map fst"

definition schedule where
  "schedule \<equiv> filter_act o snd"

definition trace where
  "trace sig \<equiv> filter (\<lambda> a . a \<in> externals sig) o schedule"

definition is_schedule_of where
  "is_schedule_of A sch \<equiv>
     (\<exists> e . is_exec_of A e \<and> sch = filter_act (snd e))"

definition is_trace_of where
  "is_trace_of A tr \<equiv>
     (\<exists> sch . is_schedule_of A sch \<and> tr = filter (\<lambda> a. a \<in> ext A) sch)"

definition traces where
  "traces A \<equiv> {tr. is_trace_of A tr}"

lemma traces_alt:
  shows "traces A = {tr . \<exists> e . is_exec_of A e 
    \<and> tr = trace (ioa.asig A) e}"
proof -
  { fix t
    assume a:"t \<in> traces A"
    have "\<exists> e . is_exec_of A e \<and> trace (ioa.asig A) e = t"
    proof -
      from a obtain sch where 1:"is_schedule_of A sch" 
        and 2:"t = filter (\<lambda> a. a \<in> ext A) sch"
        by (auto simp add:traces_def is_trace_of_def)
      from 1 obtain e where 3:"is_exec_of A e" and 4:"sch = filter_act (snd e)"
        by (auto simp add:is_schedule_of_def)
      from 4 and 2 have "trace (ioa.asig A) e = t"
        by (simp add:trace_def schedule_def)
      with 3 show ?thesis by fast
    qed }
  moreover
  { fix e
    assume "is_exec_of A e"
    hence "trace (ioa.asig A) e \<in> traces A"
      by (force simp add:trace_def schedule_def traces_def 
          is_trace_of_def is_schedule_of_def is_exec_of_def) }
  ultimately show ?thesis by blast
qed

lemmas trace_simps = traces_def is_trace_of_def is_schedule_of_def filter_act_def is_exec_of_def
  trace_def schedule_def

definition proj_trace::"'a trace \<Rightarrow> ('a signature) \<Rightarrow> 'a trace" (infixr "\<bar>" 12) where
  "proj_trace t sig \<equiv> filter (\<lambda> a . a \<in> actions sig) t"

definition ioa_implements :: "('s1,'a)ioa \<Rightarrow> ('s2,'a)ioa \<Rightarrow> bool"   (infixr "=<|" 12) where
  "A =<| B \<equiv> inp A = inp B \<and> out A = out B \<and> traces A \<subseteq> traces B"

subsection \<open>Operations on Executions\<close>

definition cons_exec where
  "cons_exec e p \<equiv> (fst e, (snd e)#p)"

definition append_exec where
  "append_exec e e' \<equiv> (fst e, (snd e)@(snd e'))"

fun last_state where
  "last_state (s,[]) = s"
| "last_state (s,ps#p) = snd p"

lemma last_state_reachable:
  fixes A e
  assumes "is_exec_of A e"
  shows "reachable A (last_state e)" using assms
proof -
  have "is_exec_of A e \<Longrightarrow> reachable A (last_state e)"
  proof (induction "snd e" arbitrary: e)
    case Nil
    from Nil.prems have 1:"fst e \<in> start A" by (simp add:is_exec_of_def)
    from Nil.hyps have 2:"last_state e = fst e" by (metis last_state.simps(1) surjective_pairing)
    from 1 and 2 and Nil.hyps show ?case by (metis reachable_0)
  next
    case (Cons p ps e)
    let ?e' = "(fst e, ps)"
    have ih:"reachable A (last_state ?e')"
    proof -
      from Cons.prems and Cons.hyps(2) have "is_exec_of A ?e'"
        by (simp add:is_exec_of_def)
          (metis (full_types) IOA.is_exec_frag_of.simps(1) IOA.is_exec_frag_of.simps(3) 
            neq_Nil_conv prod.collapse) 
      with Cons.hyps(1) show ?thesis by auto
    qed
    from Cons.prems and Cons.hyps(2) have "(last_state ?e')\<midarrow>(fst p)\<midarrow>A\<longrightarrow>(snd p)"
      by (simp add:is_exec_of_def) (cases "(A,fst e,ps#p)" rule:is_exec_frag_of.cases, auto)
    with ih and Cons.hyps(2) show ?case
      by (metis last_state.simps(2) reachable.simps surjective_pairing)
  qed
  thus ?thesis using assms by fastforce
qed

lemma trans_from_last_state:
  assumes "is_exec_frag_of A e" and "(last_state e)\<midarrow>a\<midarrow>A\<longrightarrow>s'"
  shows "is_exec_frag_of A (cons_exec e  (a,s'))"
    using assms by (cases "(A, fst e, snd e)" rule:is_exec_frag_of.cases, auto simp add:cons_exec_def)

lemma exec_frag_prefix:
  fixes A p ps
  assumes "is_exec_frag_of A (cons_exec e p)"
  shows "is_exec_frag_of A e"
    using assms by (cases "(A, fst e, snd e)" rule:is_exec_frag_of.cases, auto simp add:cons_exec_def)

lemma trace_same_ext:
  fixes A B e
  assumes "ext A = ext B"
  shows "trace (ioa.asig A) e = trace (ioa.asig B) e" 
  using assms by (auto simp add:trace_def)

lemma trace_append_is_append_trace:
  fixes e e' sig
  shows "trace sig (append_exec e' e) = trace sig e' @ trace sig e"
  by (simp add:append_exec_def trace_def schedule_def filter_act_def)

lemma append_exec_frags_is_exec_frag:
  fixes e e' A as
  assumes "is_exec_frag_of A e" and "last_state e = fst e'" 
  and "is_exec_frag_of A e'"
  shows "is_exec_frag_of A (append_exec e e')"
proof -
  from assms show ?thesis
  proof (induct "(fst e',snd e')" arbitrary:e' rule:is_exec_frag_of.induct)
    case (3 A)
    from "3.hyps" and "3.prems"(1)
    show ?case by (simp add:append_exec_def)
  next
    case (2 A p)
    have "last_state e \<midarrow>(fst p)\<midarrow>A\<longrightarrow> snd p" using "2.prems"(2,3) and "2.hyps" 
      by (metis is_exec_frag_of.simps(2) prod.collapse)
    hence "is_exec_frag_of A (fst e, (snd e)#p)" using "2.prems"(1) 
      by (metis cons_exec_def prod.collapse trans_from_last_state)
    moreover 
    have "append_exec e e' = (fst e, (snd e)#p)" using "2.hyps" 
      by (metis append_Cons append_Nil append_exec_def)
    ultimately 
    show ?case by auto
  next
    case (1 A ps p' p e')
    have "is_exec_frag_of A (fst e, (snd e)@((ps#p')#p))"
    proof -
      have "is_exec_frag_of A (fst e, (snd e)@(ps#p'))" 
        by (metis "1.hyps" "1.prems" append_exec_def cons_exec_def 
            exec_frag_prefix fst_conv prod_eqI snd_conv)
      moreover
      have "snd p' \<midarrow>(fst p)\<midarrow>A\<longrightarrow> snd p" using "1.prems"(3) "1.hyps"(2) 
        by (metis is_exec_frag_of.simps(1) prod.collapse)
      ultimately show ?thesis by simp
    qed
    moreover have "append_exec e e' = (fst e, (snd e)@((ps#p')#p))" 
      by (metis "1.hyps"(2) append_exec_def)
    ultimately show ?case by simp
  qed
qed

lemma last_state_of_append:
  fixes e e'
  assumes "fst e' = last_state e"
  shows "last_state (append_exec e e') = last_state e'"
  using assms by (cases e' rule:last_state.cases, auto simp add:append_exec_def)

end

end
