(*  Title:      JinjaThreads/Common/Type.thy
    Author:     David von Oheimb, Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory Common/Type.thy by David von Oheimb and Tobias Nipkow
*)

chapter \<open>Concepts for all JinjaThreads Languages \label{cha:j}\<close>

section \<open>JinjaThreads types\<close>

theory Type
imports
  "../Basic/Auxiliary"
begin

type_synonym cname = String.literal \<comment> \<open>class names\<close>
type_synonym mname = String.literal \<comment> \<open>method name\<close>
type_synonym vname = String.literal \<comment> \<open>names for local/field variables\<close>

definition Object :: cname
where "Object \<equiv> STR ''java/lang/Object''"

definition Thread :: cname
where "Thread \<equiv> STR ''java/lang/Thread''"

definition Throwable :: cname
where "Throwable \<equiv> STR ''java/lang/Throwable''"

definition this :: vname
where "this \<equiv> STR ''this''"

definition run :: mname
where "run \<equiv> STR ''run()V''"

definition start :: mname
where "start \<equiv> STR ''start()V''"

definition wait :: mname
where "wait \<equiv> STR ''wait()V''"

definition notify :: mname
where "notify \<equiv> STR ''notify()V''"

definition notifyAll :: mname
where "notifyAll \<equiv> STR ''notifyAll()V''"

definition join :: mname
where "join \<equiv> STR ''join()V''"

definition interrupt :: mname
where "interrupt \<equiv> STR ''interrupt()V''"

definition isInterrupted :: mname
where "isInterrupted \<equiv> STR ''isInterrupted()Z''"

(* Method names for Class Object *)

definition hashcode :: mname
where "hashcode = STR ''hashCode()I''"

definition clone :: mname
where "clone = STR ''clone()Ljava/lang/Object;''"

definition print :: mname
where "print = STR ''~print(I)V''"

definition currentThread :: mname
where "currentThread = STR ''~Thread.currentThread()Ljava/lang/Thread;''"

definition interrupted :: mname
where "interrupted = STR ''~Thread.interrupted()Z''"

definition yield :: mname
where "yield = STR ''~Thread.yield()V''"

lemmas identifier_name_defs [code_unfold] =
  this_def run_def start_def wait_def notify_def notifyAll_def join_def interrupt_def isInterrupted_def
  hashcode_def clone_def print_def currentThread_def interrupted_def yield_def

lemma Object_Thread_Throwable_neq [simp]:
  "Thread \<noteq> Object" "Object \<noteq> Thread"
  "Object \<noteq> Throwable" "Throwable \<noteq> Object"
  "Thread \<noteq> Throwable" "Throwable \<noteq> Thread"
by(auto simp add: Thread_def Object_def Throwable_def)

lemma synth_method_names_neq_aux:
  "start \<noteq> wait" "start \<noteq> notify" "start \<noteq> notifyAll" "start \<noteq> join" "start \<noteq> interrupt" "start \<noteq> isInterrupted"
  "start \<noteq> hashcode" "start \<noteq> clone" "start \<noteq> print" "start \<noteq> currentThread"
  "start \<noteq> interrupted" "start \<noteq> yield" "start \<noteq> run"
  "wait \<noteq> notify" "wait \<noteq> notifyAll" "wait \<noteq> join"  "wait \<noteq> interrupt" "wait \<noteq> isInterrupted"
  "wait \<noteq> hashcode" "wait \<noteq> clone" "wait \<noteq> print" "wait \<noteq> currentThread" 
  "wait \<noteq> interrupted" "wait \<noteq> yield"  "wait \<noteq> run"
  "notify \<noteq> notifyAll" "notify \<noteq> join" "notify \<noteq> interrupt" "notify \<noteq> isInterrupted"
  "notify \<noteq> hashcode" "notify \<noteq> clone" "notify \<noteq> print" "notify \<noteq> currentThread"
  "notify \<noteq> interrupted" "notify \<noteq> yield" "notify \<noteq> run"
  "notifyAll \<noteq> join" "notifyAll \<noteq> interrupt" "notifyAll \<noteq> isInterrupted"
  "notifyAll \<noteq> hashcode" "notifyAll \<noteq> clone" "notifyAll \<noteq> print" "notifyAll \<noteq> currentThread"
  "notifyAll \<noteq> interrupted" "notifyAll \<noteq> yield" "notifyAll \<noteq> run"
  "join \<noteq> interrupt" "join \<noteq> isInterrupted"
  "join \<noteq> hashcode" "join \<noteq> clone" "join \<noteq> print" "join \<noteq> currentThread" 
  "join \<noteq> interrupted" "join \<noteq> yield" "join \<noteq> run"
  "interrupt \<noteq> isInterrupted"
  "interrupt \<noteq> hashcode" "interrupt \<noteq> clone" "interrupt \<noteq> print" "interrupt \<noteq> currentThread" 
  "interrupt \<noteq> interrupted" "interrupt \<noteq> yield" "interrupt \<noteq> run"
  "isInterrupted \<noteq> hashcode" "isInterrupted \<noteq> clone" "isInterrupted \<noteq> print" "isInterrupted \<noteq> currentThread" 
  "isInterrupted \<noteq> interrupted" "isInterrupted \<noteq> yield" "isInterrupted \<noteq> run"
  "hashcode \<noteq> clone" "hashcode \<noteq> print" "hashcode \<noteq> currentThread" 
  "hashcode \<noteq> interrupted" "hashcode \<noteq> yield" "hashcode \<noteq> run"
  "clone \<noteq> print" "clone \<noteq> currentThread" 
  "clone \<noteq> interrupted" "clone \<noteq> yield" "clone \<noteq> run"
  "print \<noteq> currentThread" 
  "print \<noteq> interrupted" "print \<noteq> yield" "print \<noteq> run"
  "currentThread \<noteq> interrupted" "currentThread \<noteq> yield" "currentThread \<noteq> run"
  "interrupted \<noteq> yield" "interrupted \<noteq> run"
  "yield \<noteq> run"
by(simp_all add: identifier_name_defs)

lemmas synth_method_names_neq [simp] = synth_method_names_neq_aux synth_method_names_neq_aux[symmetric]

\<comment> \<open>types\<close>
datatype ty
  = Void          \<comment> \<open>type of statements\<close>
  | Boolean
  | Integer
  | NT            \<comment> \<open>null type\<close>
  | Class cname   \<comment> \<open>class type\<close>
  | Array ty      ("_\<lfloor>\<rceil>" 95) \<comment> \<open>array type\<close>

context
  notes [[inductive_internals]]
begin

inductive is_refT :: "ty \<Rightarrow> bool" where
  "is_refT NT"
| "is_refT (Class C)"
| "is_refT (A\<lfloor>\<rceil>)"

declare is_refT.intros[iff]

end

lemmas refTE [consumes 1, case_names NT Class Array] = is_refT.cases

lemma not_refTE [consumes 1, case_names Void Boolean Integer]:
  "\<lbrakk> \<not>is_refT T; T = Void \<Longrightarrow> P; T = Boolean \<Longrightarrow> P; T = Integer \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by (cases T, auto)

fun ground_type :: "ty \<Rightarrow> ty" where
  "ground_type (Array T) = ground_type T"
| "ground_type T = T"

abbreviation is_NT_Array :: "ty \<Rightarrow> bool" where
  "is_NT_Array T \<equiv> ground_type T = NT"

primrec the_Class :: "ty \<Rightarrow> cname"
where
  "the_Class (Class C) = C"

primrec the_Array :: "ty \<Rightarrow> ty"
where
  "the_Array (T\<lfloor>\<rceil>) = T"


datatype htype =
  Class_type "cname"
| Array_type "ty" "nat"

primrec ty_of_htype :: "htype \<Rightarrow> ty"
where
  "ty_of_htype (Class_type C) = Class C"
| "ty_of_htype (Array_type T n) = Array T"

primrec alen_of_htype :: "htype \<Rightarrow> nat"
where
  "alen_of_htype (Array_type T n) = n"

primrec class_type_of :: "htype \<Rightarrow> cname"
where 
  "class_type_of (Class_type C) = C"
| "class_type_of (Array_type T n) = Object"

fun class_type_of' :: "ty \<Rightarrow> cname option"
where 
  "class_type_of' (Class C) = \<lfloor>C\<rfloor>"
| "class_type_of' (Array T) = \<lfloor>Object\<rfloor>"
| "class_type_of' _ = None" 

lemma rec_htype_is_case [simp]: "rec_htype = case_htype"
by(auto simp add: fun_eq_iff split: htype.split)

lemma ty_of_htype_eq_convs [simp]:
  shows ty_of_htype_eq_Boolean: "ty_of_htype hT \<noteq> Boolean"
  and ty_of_htype_eq_Void: "ty_of_htype hT \<noteq> Void"
  and ty_of_htype_eq_Integer: "ty_of_htype hT \<noteq> Integer"
  and ty_of_htype_eq_NT: "ty_of_htype hT \<noteq> NT"
  and ty_of_htype_eq_Class: "ty_of_htype hT = Class C \<longleftrightarrow> hT = Class_type C"
  and ty_of_htype_eq_Array: "ty_of_htype hT = Array T \<longleftrightarrow> (\<exists>n. hT = Array_type T n)"
by(case_tac [!] hT) simp_all

lemma class_type_of_eq:
  "class_type_of hT = 
  (case hT of Class_type C \<Rightarrow> C | Array_type T n \<Rightarrow> Object)"
by(simp split: htype.split)

lemma class_type_of'_ty_of_htype [simp]:
  "class_type_of' (ty_of_htype hT) = \<lfloor>class_type_of hT\<rfloor>"
by(cases hT) simp_all

fun is_Array :: "ty \<Rightarrow> bool"
where
  "is_Array (Array T) = True"
| "is_Array _ = False"

lemma is_Array_conv [simp]: "is_Array T \<longleftrightarrow> (\<exists>U. T = Array U)"
by(cases T) simp_all

fun is_Class :: "ty \<Rightarrow> bool"
where
  "is_Class (Class C) = True"
| "is_Class _ = False"

lemma is_Class_conv [simp]: "is_Class T \<longleftrightarrow> (\<exists>C. T = Class C)"
by(cases T) simp_all

subsection \<open>Code generator setup\<close>

code_pred is_refT .

end
