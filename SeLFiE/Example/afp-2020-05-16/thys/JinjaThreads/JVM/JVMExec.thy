(*  Title:      JinjaThreads/JVM/JVMExec.thy
    Author:     Cornelia Pusch, Gerwin Klein, Andreas Lochbihler
*)

section \<open>Program Execution in the JVM\<close>

theory JVMExec
imports
  JVMExecInstr
  JVMExceptions
  "../Common/StartConfig"
begin

abbreviation instrs_of :: "'addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> 'addr instr list"
where "instrs_of P C M == fst(snd(snd(the(snd(snd(snd(method P C M)))))))"

subsection "single step execution"

context JVM_heap_base begin

fun exception_step :: "'addr jvm_prog \<Rightarrow> 'addr \<Rightarrow> 'heap \<Rightarrow> 'addr frame \<Rightarrow> 'addr frame list \<Rightarrow> ('addr, 'heap) jvm_state"
where
  "exception_step P a h (stk, loc, C, M, pc) frs = 
   (case match_ex_table P (cname_of h a) pc (ex_table_of P C M) of
          None \<Rightarrow> (\<lfloor>a\<rfloor>, h, frs)
        | Some (pc', d) \<Rightarrow> (None, h, (Addr a # drop (size stk - d) stk, loc, C, M, pc') # frs))"

lemma exception_step_def_raw:
  "exception_step = 
   (\<lambda>P a h (stk, loc, C, M, pc) frs.
    case match_ex_table P (cname_of h a) pc (ex_table_of P C M) of
      None \<Rightarrow> (\<lfloor>a\<rfloor>, h, frs)
    | Some (pc', d) \<Rightarrow> (None, h, (Addr a # drop (size stk - d) stk, loc, C, M, pc') # frs))"
by(intro ext) auto

fun exec :: "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_ta_state set" where
  "exec P t (xcp, h, []) = {}"
| "exec P t (None, h, (stk, loc, C, M, pc) # frs) = exec_instr (instrs_of P C M ! pc) P t h stk loc C M pc frs"
| "exec P t (\<lfloor>a\<rfloor>, h, fr # frs) = {(\<epsilon>, exception_step P a h fr frs)}"

subsection "relational view"

inductive exec_1 :: 
  "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'heap) jvm_state
  \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> bool"
  ("_,_ \<turnstile>/ _ -_-jvm\<rightarrow>/ _" [61,0,61,0,61] 60)
  for P :: "'addr jvm_prog" and t :: 'thread_id
where
  exec_1I:
  "(ta, \<sigma>') \<in> exec P t \<sigma> \<Longrightarrow> P,t \<turnstile> \<sigma> -ta-jvm\<rightarrow> \<sigma>'"

lemma exec_1_iff:
  "P,t \<turnstile> \<sigma> -ta-jvm\<rightarrow> \<sigma>' \<longleftrightarrow> (ta, \<sigma>') \<in> exec P t \<sigma>"
by(auto intro: exec_1I elim: exec_1.cases)

end

text \<open>
  The start configuration of the JVM: in the start heap, we call a 
  method \<open>m\<close> of class \<open>C\<close> in program \<open>P\<close> with parameters @{term "vs"}. The 
  \<open>this\<close> pointer of the frame is set to \<open>Null\<close> to simulate
  a static method invokation.
\<close>

abbreviation JVM_local_start ::
  "cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'addr jvm_method \<Rightarrow> 'addr val list
  \<Rightarrow> 'addr jvm_thread_state"
where
  "JVM_local_start \<equiv> 
   \<lambda>C M Ts T (mxs, mxl0, b) vs. 
   (None, [([], Null # vs @ replicate mxl0 undefined_value, C, M, 0)])"

context JVM_heap_base begin

abbreviation JVM_start_state :: 
  "'addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> ('addr,'thread_id,'addr jvm_thread_state,'heap,'addr) state"
where
  "JVM_start_state \<equiv> start_state JVM_local_start"

definition JVM_start_state' :: "'addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> ('addr, 'heap) jvm_state"
where
  "JVM_start_state' P C M vs \<equiv>
   let (D, Ts, T, meth) = method P C M;
       (mxs, mxl0, ins, xt) = the meth
   in (None, start_heap, [([], Null # vs @ replicate mxl0 undefined_value, D, M, 0)])"

end

end
