(*  Title:      JinjaThreads/Common/Exceptions.thy
    Author:     Gerwin Klein, Martin Strecker, Andreas Lochbihler

    Based on the Jinja theory Common/Exceptions.thy by Gerwin Klein and Martin Strecker
*)

section \<open>Exceptions\<close>

theory Exceptions
imports
  Value
begin

definition NullPointer :: cname
where [code_unfold]: "NullPointer = STR ''java/lang/NullPointerException''"

definition ClassCast :: cname
where [code_unfold]: "ClassCast = STR ''java/lang/ClassCastException''"

definition OutOfMemory :: cname
where [code_unfold]: "OutOfMemory = STR ''java/lang/OutOfMemoryError''"

definition ArrayIndexOutOfBounds :: cname
where [code_unfold]: "ArrayIndexOutOfBounds = STR ''java/lang/ArrayIndexOutOfBoundsException''"

definition ArrayStore :: cname
where [code_unfold]: "ArrayStore = STR ''java/lang/ArrayStoreException''"

definition NegativeArraySize :: cname
where [code_unfold]: "NegativeArraySize = STR ''java/lang/NegativeArraySizeException''"

definition ArithmeticException :: cname
where [code_unfold]: "ArithmeticException = STR ''java/lang/ArithmeticException''"

definition IllegalMonitorState :: cname
where [code_unfold]: "IllegalMonitorState = STR ''java/lang/IllegalMonitorStateException''"

definition IllegalThreadState :: cname
where [code_unfold]: "IllegalThreadState = STR ''java/lang/IllegalThreadStateException''"

definition InterruptedException :: cname
where [code_unfold]: "InterruptedException = STR ''java/lang/InterruptedException''"

definition sys_xcpts_list :: "cname list"
where
  "sys_xcpts_list = 
  [NullPointer, ClassCast, OutOfMemory, ArrayIndexOutOfBounds, ArrayStore, NegativeArraySize, ArithmeticException,
   IllegalMonitorState, IllegalThreadState, InterruptedException]"

definition sys_xcpts :: "cname set"
where [code_unfold]: "sys_xcpts = set sys_xcpts_list"

definition wf_syscls :: "'m prog \<Rightarrow> bool"
where "wf_syscls P \<equiv> (\<forall>C \<in> {Object, Throwable, Thread}. is_class P C) \<and> (\<forall>C \<in> sys_xcpts. P \<turnstile> C \<preceq>\<^sup>* Throwable)"

subsection "System exceptions"

lemma [simp]:
  "NullPointer \<in> sys_xcpts \<and> 
   OutOfMemory \<in> sys_xcpts \<and> 
   ClassCast \<in> sys_xcpts \<and> 
   ArrayIndexOutOfBounds \<in> sys_xcpts \<and> 
   ArrayStore \<in> sys_xcpts \<and> 
   NegativeArraySize \<in> sys_xcpts \<and> 
   IllegalMonitorState \<in> sys_xcpts \<and>
   IllegalThreadState \<in> sys_xcpts \<and>
   InterruptedException \<in> sys_xcpts \<and>
   ArithmeticException \<in> sys_xcpts"
by(simp add: sys_xcpts_def sys_xcpts_list_def)

lemma sys_xcpts_cases [consumes 1, cases set]:
  "\<lbrakk> C \<in> sys_xcpts; P NullPointer; P OutOfMemory; P ClassCast; 
     P ArrayIndexOutOfBounds; P ArrayStore; P NegativeArraySize;
     P ArithmeticException;
     P IllegalMonitorState; P IllegalThreadState; P InterruptedException \<rbrakk>
  \<Longrightarrow> P C"
by (auto simp add: sys_xcpts_def sys_xcpts_list_def)

lemma OutOfMemory_not_Object[simp]: "OutOfMemory \<noteq> Object"
by(simp add: OutOfMemory_def Object_def)

lemma ClassCast_not_Object[simp]: "ClassCast \<noteq> Object"
by(simp add: ClassCast_def Object_def)

lemma NullPointer_not_Object[simp]: "NullPointer \<noteq> Object"
by(simp add: NullPointer_def Object_def)

lemma ArrayIndexOutOfBounds_not_Object[simp]: "ArrayIndexOutOfBounds \<noteq> Object"
by(simp add: ArrayIndexOutOfBounds_def Object_def)

lemma ArrayStore_not_Object[simp]: "ArrayStore \<noteq> Object"
by(simp add: ArrayStore_def Object_def)

lemma NegativeArraySize_not_Object[simp]: "NegativeArraySize \<noteq> Object"
by(simp add: NegativeArraySize_def Object_def)

lemma ArithmeticException_not_Object[simp]: "ArithmeticException \<noteq> Object"
by(simp add: ArithmeticException_def Object_def)

lemma IllegalMonitorState_not_Object[simp]: "IllegalMonitorState \<noteq> Object"
by(simp add: IllegalMonitorState_def Object_def)

lemma IllegalThreadState_not_Object[simp]: "IllegalThreadState \<noteq> Object"
by(simp add: IllegalThreadState_def Object_def)

lemma InterruptedException_not_Object[simp]: "InterruptedException \<noteq> Object"
by(simp add: InterruptedException_def Object_def)

lemma sys_xcpts_neqs_aux:
  "NullPointer \<noteq> ClassCast" "NullPointer \<noteq> OutOfMemory" "NullPointer \<noteq> ArrayIndexOutOfBounds"
  "NullPointer \<noteq> ArrayStore" "NullPointer \<noteq> NegativeArraySize" "NullPointer \<noteq> IllegalMonitorState"
  "NullPointer \<noteq> IllegalThreadState" "NullPointer \<noteq> InterruptedException" "NullPointer \<noteq> ArithmeticException"
  "ClassCast \<noteq> OutOfMemory" "ClassCast \<noteq> ArrayIndexOutOfBounds"
  "ClassCast \<noteq> ArrayStore" "ClassCast \<noteq> NegativeArraySize" "ClassCast \<noteq> IllegalMonitorState"
  "ClassCast \<noteq> IllegalThreadState" "ClassCast \<noteq> InterruptedException" "ClassCast \<noteq> ArithmeticException"
  "OutOfMemory \<noteq> ArrayIndexOutOfBounds"
  "OutOfMemory \<noteq> ArrayStore" "OutOfMemory \<noteq> NegativeArraySize" "OutOfMemory \<noteq> IllegalMonitorState"
  "OutOfMemory \<noteq> IllegalThreadState" "OutOfMemory \<noteq> InterruptedException"
  "OutOfMemory \<noteq> ArithmeticException"
  "ArrayIndexOutOfBounds \<noteq> ArrayStore" "ArrayIndexOutOfBounds \<noteq> NegativeArraySize" "ArrayIndexOutOfBounds \<noteq> IllegalMonitorState"
  "ArrayIndexOutOfBounds \<noteq> IllegalThreadState" "ArrayIndexOutOfBounds \<noteq> InterruptedException" "ArrayIndexOutOfBounds \<noteq> ArithmeticException"
  "ArrayStore \<noteq> NegativeArraySize" "ArrayStore \<noteq> IllegalMonitorState"
  "ArrayStore \<noteq> IllegalThreadState" "ArrayStore \<noteq> InterruptedException"
  "ArrayStore \<noteq> ArithmeticException"
  "NegativeArraySize \<noteq> IllegalMonitorState"
  "NegativeArraySize \<noteq> IllegalThreadState" "NegativeArraySize \<noteq> InterruptedException"
  "NegativeArraySize \<noteq> ArithmeticException"
  "IllegalMonitorState \<noteq> IllegalThreadState" "IllegalMonitorState \<noteq> InterruptedException"
  "IllegalMonitorState \<noteq> ArithmeticException"
  "IllegalThreadState \<noteq> InterruptedException"
  "IllegalThreadState \<noteq> ArithmeticException"
  "InterruptedException \<noteq> ArithmeticException"
by(simp_all add: NullPointer_def ClassCast_def OutOfMemory_def ArrayIndexOutOfBounds_def ArrayStore_def NegativeArraySize_def IllegalMonitorState_def IllegalThreadState_def InterruptedException_def ArithmeticException_def)

lemmas sys_xcpts_neqs = sys_xcpts_neqs_aux sys_xcpts_neqs_aux[symmetric]

lemma Thread_neq_sys_xcpts_aux:
  "Thread \<noteq> NullPointer"
  "Thread \<noteq> ClassCast"
  "Thread \<noteq> OutOfMemory"
  "Thread \<noteq> ArrayIndexOutOfBounds"
  "Thread \<noteq> ArrayStore"
  "Thread \<noteq> NegativeArraySize"
  "Thread \<noteq> ArithmeticException"
  "Thread \<noteq> IllegalMonitorState"
  "Thread \<noteq> IllegalThreadState"
  "Thread \<noteq> InterruptedException"
by(simp_all add: Thread_def NullPointer_def ClassCast_def OutOfMemory_def ArrayIndexOutOfBounds_def ArrayStore_def NegativeArraySize_def IllegalMonitorState_def IllegalThreadState_def InterruptedException_def ArithmeticException_def)

lemmas Thread_neq_sys_xcpts = Thread_neq_sys_xcpts_aux Thread_neq_sys_xcpts_aux[symmetric]

subsection \<open>Well-formedness for system classes and exceptions\<close>

lemma
  assumes "wf_syscls P"
  shows wf_syscls_class_Object: "\<exists>C fs ms. class P Object = Some (C,fs,ms)"
  and wf_syscls_class_Thread:  "\<exists>C fs ms. class P Thread = Some (C,fs,ms)"
using assms
by(auto simp: map_of_SomeI wf_syscls_def is_class_def)

lemma [simp]:
  assumes "wf_syscls P"
  shows wf_syscls_is_class_Object: "is_class P Object"
  and wf_syscls_is_class_Thread: "is_class P Thread"
using assms by(simp_all add: is_class_def wf_syscls_class_Object wf_syscls_class_Thread)

lemma wf_syscls_xcpt_subcls_Throwable:
  "\<lbrakk> C \<in> sys_xcpts; wf_syscls P \<rbrakk> \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* Throwable"
by(simp add: wf_syscls_def is_class_def class_def)

lemma wf_syscls_is_class_Throwable:
  "wf_syscls P \<Longrightarrow> is_class P Throwable"
by(auto simp add: wf_syscls_def is_class_def class_def map_of_SomeI)

lemma wf_syscls_is_class_sub_Throwable:
  "\<lbrakk> wf_syscls P; P \<turnstile> C \<preceq>\<^sup>* Throwable \<rbrakk> \<Longrightarrow> is_class P C"
by(erule subcls_is_class1)(erule wf_syscls_is_class_Throwable)

lemma wf_syscls_is_class_xcpt:
  "\<lbrakk> C \<in> sys_xcpts; wf_syscls P \<rbrakk> \<Longrightarrow> is_class P C"
by(blast intro: wf_syscls_is_class_sub_Throwable wf_syscls_xcpt_subcls_Throwable)

lemma wf_syscls_code [code]:
  "wf_syscls P \<longleftrightarrow>
   (\<forall>C \<in> set [Object, Throwable, Thread]. is_class P C) \<and> (\<forall>C \<in> sys_xcpts. P \<turnstile> C \<preceq>\<^sup>* Throwable)"
by(simp only: wf_syscls_def) simp

end
