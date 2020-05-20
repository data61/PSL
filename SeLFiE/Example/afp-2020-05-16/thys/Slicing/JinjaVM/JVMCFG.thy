(* This work was done by Denis Lohner (denis.lohner@kit.edu). *)

chapter \<open>A Control Flow Graph for Jinja Byte Code\<close>

section \<open>Formalizing the CFG\<close>

theory JVMCFG imports "../Basic/BasicDefs" Jinja.BVExample begin


declare lesub_list_impl_same_size [simp del]
declare listE_length [simp del]

subsection \<open>Type definitions\<close>

subsubsection \<open>Wellformed Programs\<close>

definition "wf_jvmprog = {(P, Phi). wf_jvm_prog\<^bsub>Phi\<^esub> P}"

typedef wf_jvmprog = wf_jvmprog
proof
  show "(E, Phi) \<in> wf_jvmprog"
    unfolding wf_jvmprog_def by (auto intro: wf_prog)
qed

hide_const Phi E

abbreviation rep_jvmprog_jvm_prog :: "wf_jvmprog \<Rightarrow> jvm_prog"
("_\<^bsub>wf\<^esub>")
  where "P\<^bsub>wf\<^esub> \<equiv> fst(Rep_wf_jvmprog(P))"

abbreviation rep_jvmprog_phi :: "wf_jvmprog \<Rightarrow> ty\<^sub>P"
("_\<^bsub>\<Phi>\<^esub>")
  where "P\<^bsub>\<Phi>\<^esub> \<equiv> snd(Rep_wf_jvmprog(P))"

lemma wf_jvmprog_is_wf: "wf_jvm_prog\<^bsub>P\<^bsub>\<Phi>\<^esub>\<^esub> (P\<^bsub>wf\<^esub>)"
using Rep_wf_jvmprog [of P]
  by (auto simp: wf_jvmprog_def split_beta)

subsubsection \<open>Basic Types\<close>

text \<open>
We consider a program to be a well-formed Jinja program,
together with a given base class and a main method
\<close>

type_synonym jvmprog = "wf_jvmprog \<times> cname \<times> mname"
type_synonym callstack = "(cname \<times> mname \<times> pc) list"

text \<open>
The state is modeled as $\textrm{heap} \times \textrm{stack-variables} \times \textrm{local-variables}$

stack and local variables are modeled as pairs of natural numbers. The first number
gives the position in the call stack (i.e. the method in which the variable is used),
the second the position in the method's stack or array of local variables resp.

The stack variables are numbered from bottom up (which is the reverse order of the
array for the stack in Jinja's state representation), whereas local variables are identified
by their position in the array of local variables of Jinja's state representation.
\<close>

type_synonym state = "heap \<times> ((nat \<times> nat) \<Rightarrow> val) \<times> ((nat \<times> nat) \<Rightarrow> val)"


abbreviation heap_of :: "state \<Rightarrow> heap"
where
  "heap_of s \<equiv> fst(s)"

abbreviation stk_of :: "state \<Rightarrow> ((nat \<times> nat) \<Rightarrow> val)"
where
  "stk_of s \<equiv> fst(snd(s))"

abbreviation loc_of :: "state \<Rightarrow> ((nat \<times> nat) \<Rightarrow> val)"
where
  "loc_of s \<equiv> snd(snd(s))"


subsection \<open>Basic Definitions\<close>

subsubsection \<open>State update (instruction execution)\<close>

text \<open>
This function models instruction execution for our state representation.

Additional parameters are the call depth of the current program point,
the stack length of the current program point,
the length of the stack in the underlying call frame (needed for {\sc Return}),
and (for {\sc Invoke}) the length of the array of local variables of the invoked method.

Exception handling is not covered by this function.
\<close>

fun exec_instr :: "instr \<Rightarrow> wf_jvmprog \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state"
where
  exec_instr_Load:
  "exec_instr (Load n) P s calldepth stk_length rs ill =
  (let (h,stk,loc) = s
   in (h, stk((calldepth,stk_length):=loc(calldepth,n)), loc))"

| exec_instr_Store:
  "exec_instr (Store n) P s calldepth stk_length rs ill =
  (let (h,stk,loc) = s
   in (h, stk, loc((calldepth,n):=stk(calldepth,stk_length - 1))))"

| exec_instr_Push:
  "exec_instr (Push v) P s calldepth stk_length rs ill =
  (let (h,stk,loc) = s
   in (h, stk((calldepth,stk_length):=v), loc))"

| exec_instr_New:
  "exec_instr (New C) P s calldepth stk_length rs ill =
  (let (h,stk,loc) = s;
    a = the(new_Addr h)
   in (h(a \<mapsto> (blank (P\<^bsub>wf\<^esub>) C)), stk((calldepth,stk_length):=Addr a), loc))"

| exec_instr_Getfield:
  "exec_instr (Getfield F C) P s calldepth stk_length rs ill =
  (let (h,stk,loc) = s;
    a = the_Addr (stk (calldepth,stk_length - 1));
    (D,fs) = the(h a)
   in (h, stk((calldepth,stk_length - 1) := the(fs(F,C))), loc))"

| exec_instr_Putfield:
  "exec_instr (Putfield F C) P s calldepth stk_length rs ill =
  (let (h,stk,loc) = s;
    v = stk (calldepth,stk_length - 1);
    a = the_Addr (stk (calldepth,stk_length - 2));
    (D,fs) = the(h a)
   in (h(a \<mapsto> (D,fs((F,C) \<mapsto> v))), stk, loc))"

| exec_instr_Checkcast:
  "exec_instr (Checkcast C) P s calldepth stk_length rs ill = s"

| exec_instr_Pop:
  "exec_instr (Pop) P s calldepth stk_length rs ill = s"

| exec_instr_IAdd:
  "exec_instr (IAdd) P s calldepth stk_length rs ill =
  (let (h,stk,loc) = s;
    i\<^sub>1 = the_Intg (stk (calldepth, stk_length - 1));
    i\<^sub>2 = the_Intg (stk (calldepth, stk_length - 2))
   in (h, stk((calldepth, stk_length - 2) := Intg (i\<^sub>1 + i\<^sub>2)), loc))"

| exec_instr_IfFalse:
  "exec_instr (IfFalse b) P s calldepth stk_length rs ill = s"

| exec_instr_CmpEq:
  "exec_instr (CmpEq) P s calldepth stk_length rs ill =
  (let (h,stk,loc) = s;
    v\<^sub>1 = stk (calldepth, stk_length - 1);
    v\<^sub>2 = stk (calldepth, stk_length - 2)
   in (h, stk((calldepth, stk_length - 2) := Bool (v\<^sub>1 = v\<^sub>2)), loc))"

| exec_instr_Goto:
  "exec_instr (Goto i) P s calldepth stk_length rs ill = s"
  
| exec_instr_Throw:
  "exec_instr (Throw) P s calldepth stk_length rs ill = s"

| exec_instr_Invoke:
  "exec_instr (Invoke M n) P s calldepth stk_length rs invoke_loc_length =
  (let (h,stk,loc) = s;
    loc' = (\<lambda>(a,b). if (a \<noteq> Suc calldepth \<or> b \<ge> invoke_loc_length) then loc(a,b) else
                      (if (b \<le> n) then stk(calldepth, stk_length - (Suc n - b)) else arbitrary))
   in (h,stk,loc'))"

| exec_instr_Return:
  "exec_instr (Return) P s calldepth stk_length ret_stk_length ill =
  (if (calldepth = 0)
    then s
    else
    (let (h,stk,loc) = s;
      v = stk(calldepth, stk_length - 1)
     in (h,stk((calldepth - 1, ret_stk_length - 1) := v),loc))
  )"


subsubsection \<open>length of stack and local variables\<close>

text \<open>The following terms extract the stack length at a given program point
from the well-typing of the given program\<close>

abbreviation stkLength :: "wf_jvmprog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> pc \<Rightarrow> nat"
  where
  "stkLength P C M pc \<equiv> length (fst(the(((P\<^bsub>\<Phi>\<^esub>) C M)!pc)))"

abbreviation locLength :: "wf_jvmprog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> pc \<Rightarrow> nat"
  where
  "locLength P C M pc \<equiv> length (snd(the(((P\<^bsub>\<Phi>\<^esub>) C M)!pc)))"


subsubsection \<open>Conversion functions\<close>

text \<open>
This function takes a natural number n and a function f with domain \<open>nat\<close>
and creates the array [f 0, f 1, f 2, ..., f (n - 1)].

This is used for extracting the array of local variables
\<close>

(*
fun locs :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list"
where
  "locs 0 loc = []"
| "locs (Suc n) loc = (locs n loc)@[loc n]"
*)

abbreviation locs :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list"
where "locs n loc \<equiv> map loc [0..<n]"

text \<open>
This function takes a natural number n and a function f with domain \<open>nat\<close>
and creates the array [f (n - 1), ..., f 1, f 0].

This is used for extracting the stack as a list
\<close>

(*
fun stks :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list"
where
  "stks 0 stk = []"
| "stks (Suc n) stk = (stk n)#(stks n stk)"
*)

abbreviation stks :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list"
where "stks n stk \<equiv> map stk (rev [0..<n])"

text \<open>
This function creates a list of the arrays for local variables from the given state
corresponding to the given callstack
\<close>

fun locss :: "wf_jvmprog \<Rightarrow> callstack \<Rightarrow> ((nat \<times> nat) \<Rightarrow> 'a) \<Rightarrow> 'a list list"
where
  "locss P [] loc = []"
| "locss P ((C,M,pc)#cs) loc =
    (locs (locLength P C M pc) (\<lambda>a. loc (length cs, a)))#(locss P cs loc)"

text \<open>
This function creates a list of the (methods') stacks from the given state
corresponding to the given callstack
\<close>

fun stkss :: "wf_jvmprog \<Rightarrow> callstack \<Rightarrow> ((nat \<times> nat) \<Rightarrow> 'a) \<Rightarrow> 'a list list"
where
  "stkss P [] stk = []"
| "stkss P ((C,M,pc)#cs) stk =
  (stks (stkLength P C M pc) (\<lambda>a. stk (length cs, a)))#(stkss P cs stk)"

text \<open>Given a callstack and a state, this abbreviation converts the state
to Jinja's state representation
\<close>

abbreviation state_to_jvm_state :: "wf_jvmprog \<Rightarrow> callstack \<Rightarrow> state \<Rightarrow> jvm_state"
where "state_to_jvm_state P cs s \<equiv> 
  (None, heap_of s, zip (stkss P cs (stk_of s)) (zip (locss P cs (loc_of s)) cs))"

text \<open>This function extracts the call stack from a given frame stack (as it is given
by Jinja's state representation)
\<close>

definition framestack_to_callstack :: "frame list \<Rightarrow> callstack"
where "framestack_to_callstack frs \<equiv> map snd (map snd frs)"


subsubsection \<open>State Conformance\<close>

text \<open>Now we lift byte code verifier conformance to our state representation\<close>

definition bv_conform :: "wf_jvmprog \<Rightarrow> callstack \<Rightarrow> state \<Rightarrow> bool"
  ("_,_ \<turnstile>\<^bsub>BV\<^esub> _ \<surd>")
where "P,cs \<turnstile>\<^bsub>BV\<^esub> s \<surd> \<equiv> correct_state (P\<^bsub>wf\<^esub>) (P\<^bsub>\<Phi>\<^esub>) (state_to_jvm_state P cs s)"


subsubsection \<open>Statically determine catch-block\<close>

text \<open>This function is equivalent to Jinja's \<open>find_handler\<close> function\<close>
fun find_handler_for :: "wf_jvmprog \<Rightarrow> cname \<Rightarrow> callstack \<Rightarrow> callstack"
where
  "find_handler_for P C [] = []"
| "find_handler_for P C (c#cs) = (let (C',M',pc') = c in
     (case match_ex_table (P\<^bsub>wf\<^esub>) C pc' (ex_table_of (P\<^bsub>wf\<^esub>) C' M') of
          None \<Rightarrow> find_handler_for P C cs
        | Some pc_d \<Rightarrow> (C', M', fst pc_d)#cs))"


subsection \<open>Simplification lemmas\<close>

lemma find_handler_decr [simp]: "find_handler_for P Exc cs \<noteq> c#cs"
proof
  assume "find_handler_for P Exc cs = c#cs"
  hence "length cs < length (find_handler_for P Exc cs)" by simp
  thus False by (induct cs, auto)
qed

(*
lemma locs_length [simp]: "length (locs n loc) = n"
  by (induct n) auto

lemma stks_length [simp]: "length (stks n stk) = n"
  by (induct n) auto
*)

lemma stkss_length [simp]: "length (stkss P cs stk) = length cs"
  by (induct cs) auto

lemma locss_length [simp]: "length (locss P cs loc) = length cs"
  by (induct cs) auto

(*
lemma nth_stks: "b < n \<Longrightarrow> stks n stk ! b = stk(n - Suc b)"
  by (auto simp: rev_nth)
proof (induct n arbitrary: b)
  case (0 b)
  thus ?case by simp
next
  case (Suc n b)
  thus ?case
    by (auto simp: nth_Cons' less_Suc_eq)
qed
*)

lemma nth_stkss: 
  "\<lbrakk> a < length cs; b < length (stkss P cs stk ! (length cs - Suc a)) \<rbrakk>
  \<Longrightarrow> stkss P cs stk ! (length cs - Suc a) ! 
    (length (stkss P cs stk ! (length cs - Suc a)) - Suc b) = stk (a,b)"
proof (induct cs)
  case Nil
  thus ?case by (simp add: nth_Cons')
next
  case (Cons aa cs)
  thus ?case
    by (cases aa, auto simp add: nth_Cons' rev_nth less_Suc_eq)
qed

(*
lemma nth_locs: "b < n \<Longrightarrow> locs n loc ! b = loc b"
proof (induct n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  thus ?case
    by (auto simp: nth_append less_Suc_eq)
qed
*)

lemma nth_locss:
  "\<lbrakk> a < length cs; b < length (locss P cs loc ! (length cs - Suc a)) \<rbrakk>
  \<Longrightarrow> locss P cs loc ! (length cs - Suc a) ! b = loc (a,b)"
proof (induct cs)
  case Nil
  thus ?case by (simp add: nth_Cons')
next
  case (Cons aa cs)
  thus ?case
    by (cases aa, auto simp: nth_Cons' (* nth_locs *) less_Suc_eq)
qed

lemma hd_stks [simp]: "n \<noteq> 0 \<Longrightarrow> hd (stks n stk) = stk(n - 1)"
  by (cases n, simp_all)

lemma hd_tl_stks: "n > 1 \<Longrightarrow> hd (tl (stks n stk)) = stk(n - 2)"
  by (cases n, auto)

(*
lemma stks_purge:
  "d \<ge> b \<Longrightarrow> stks b (stk(d := e)) = stks b stk"
  by (induct b, auto)

lemma stks_purge':
  "d \<ge> b \<Longrightarrow> stks b (\<lambda>x. if x = d then e else stk x) = stks b stk"
  by (fold fun_upd_def, simp only: stks_purge)
*)

lemma stkss_purge:
  "length cs \<le> a \<Longrightarrow> stkss P cs (stk((a,b) := c)) = stkss P cs stk"
  by (induct cs, auto (* simp: stks_purge *))

lemma stkss_purge':
  "length cs \<le> a \<Longrightarrow> stkss P cs (\<lambda>s. if s = (a, b) then c else stk s) = stkss P cs stk"
  by (fold fun_upd_def, simp only: stkss_purge)

(*
lemma locs_purge:
  "d \<ge> b \<Longrightarrow> locs b (loc(d := e)) = locs b loc"
  by (induct b, auto)

lemma locs_purge':
  "d \<ge> b \<Longrightarrow> locs b (\<lambda>b. if b = d then e else loc b) = locs b loc"
  by (fold fun_upd_def, simp only: locs_purge)
*)
 
lemma locss_purge:
  "length cs \<le> a \<Longrightarrow> locss P cs (loc((a,b) := c)) = locss P cs loc"
  by (induct cs, auto (*simp: locs_purge *))

lemma locss_purge':
  "length cs \<le> a \<Longrightarrow> locss P cs (\<lambda>s. if s = (a, b) then c else loc s) = locss P cs loc"
  by (fold fun_upd_def, simp only: locss_purge)

lemma locs_pullout [simp]:
  "locs b (loc(n := e)) = (locs b loc) [n := e]"
proof (induct b)
  case 0
  thus ?case by simp
next
  case (Suc b)
  thus ?case
    by (cases "n - b", auto simp: list_update_append not_less_eq less_Suc_eq)
qed

lemma locs_pullout' [simp]:
  "locs b (\<lambda>a. if a = n then e else loc (c, a)) = (locs b (\<lambda>a. loc (c, a))) [n := e]"
  by (fold fun_upd_def) simp

lemma stks_pullout:
  "n < b \<Longrightarrow> stks b (stk(n := e)) = (stks b stk) [b - Suc n := e]"
proof (induct b)
  case 0
  thus ?case by simp
next
  case (Suc b)
  thus ?case
  proof (cases "b = n")
    case True
    with Suc show ?thesis
      by auto
(*      by (auto simp: stks_purge') *)
  next
    case False
    with Suc show ?thesis
      by (cases "b - n") (auto intro!: nth_equalityI simp: nth_list_update)
 qed
qed

lemma nth_tl : "xs \<noteq> [] \<Longrightarrow> tl xs ! n = xs ! (Suc n)"
  by (cases xs, simp_all)

lemma f2c_Nil [simp]: "framestack_to_callstack [] = []"
  by (simp add: framestack_to_callstack_def)

lemma f2c_Cons [simp]:
  "framestack_to_callstack ((stk,loc,C,M,pc)#frs) = (C,M,pc)#(framestack_to_callstack frs)"
  by (simp add: framestack_to_callstack_def)

lemma f2c_length [simp]:
  "length (framestack_to_callstack frs) = length frs"
  by (simp add: framestack_to_callstack_def)

lemma f2c_s2jvm_id [simp]:
  "framestack_to_callstack
    (snd(snd(state_to_jvm_state P cs s))) =
  cs"
  by (cases s, simp add: framestack_to_callstack_def)

lemma f2c_s2jvm_id' [simp]:
  "framestack_to_callstack
  (zip (stkss P cs stk) (zip (locss P cs loc) cs)) = cs"
  by (simp add: framestack_to_callstack_def)

lemma f2c_append [simp]:
  "framestack_to_callstack (frs @ frs') =
  (framestack_to_callstack frs) @ (framestack_to_callstack frs')"
  by (simp add: framestack_to_callstack_def)


subsection \<open>CFG construction\<close>

subsection \<open>Datatypes\<close>

text \<open>Nodes are labeled with a callstack and an optional tuple (consisting of
a callstack and a flag).

The first callstack determines the current program point (i.e. the next statement
to execute). If the second parameter is not None, we are at an intermediate state,
where the target of the instruction is determined (the second callstack)
and the flag is set to whether an exception is thrown or not.
\<close>
datatype j_node =
   Entry  ("'('_Entry'_')")
 | Node "callstack" "(callstack \<times> bool) option" ("'('_ _,_ '_')")

text \<open>The empty callstack indicates the exit node\<close>

abbreviation j_node_Exit :: "j_node" ("'('_Exit'_')")
where "j_node_Exit \<equiv> (_ [],None _)"

text \<open>An edge is a triple, consisting of two nodes and the edge kind\<close>

type_synonym j_edge = "(j_node \<times> state edge_kind \<times> j_node)"


subsection \<open>CFG\<close>

text \<open>
The CFG is constructed by a case analysis on the instructions and
their different behavior in different states. E.g. the exceptional behavior of
{\sc New}, if there is no more space in the heap, vs. the normal behavior.

Note: The set of edges defined by this predicate is a first approximation to the
real set of edges in the CFG. We later (theory JVMInterpretation) add some well-formedness
requirements to the nodes.
\<close>

inductive JVM_CFG :: "jvmprog \<Rightarrow> j_node \<Rightarrow> state edge_kind \<Rightarrow> j_node \<Rightarrow> bool"
  ("_ \<turnstile> _ -_\<rightarrow> _")
where
  JCFG_EntryExit:
  "prog \<turnstile> (_Entry_) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (_Exit_)"

| JCFG_EntryStart:
  "prog = (P, C0, Main) \<Longrightarrow> prog \<turnstile> (_Entry_) -(\<lambda>s. True)\<^sub>\<surd>\<rightarrow> (_ [(C0, Main, 0)],None _)"

| JCFG_ReturnExit:
  "\<lbrakk> prog = (P,C0,Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = Return \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ [(C, M, pc)],None _) -\<Up>id\<rightarrow> (_Exit_)"

| JCFG_Straight_NoExc:
  "\<lbrakk> prog = (P, C0, Main);
    instrs_of (P\<^bsub>wf\<^esub>) C M ! pc \<in> {Load idx, Store idx, Push val, Pop, IAdd, CmpEq};
    ek = \<Up>(\<lambda>s. exec_instr ((instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc) P s
                          (length cs) (stkLength P C M pc) arbitrary arbitrary) \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, Suc pc)#cs,None _)"

| JCFG_New_Normal_Pred:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (New Cl);
    ek = (\<lambda>(h,stk,loc). new_Addr h \<noteq> None)\<^sub>\<surd>\<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, pc)#cs,\<lfloor>((C, M, Suc pc)#cs,False)\<rfloor> _)"

| JCFG_New_Normal_Update:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (New Cl);
    ek = \<Up>(\<lambda>s. exec_instr (New Cl) P s (length cs) (stkLength P C M pc) arbitrary arbitrary) \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>((C, M, Suc pc)#cs, False)\<rfloor> _) -ek\<rightarrow> (_ (C, M, Suc pc)#cs,None _)"

| JCFG_New_Exc_Pred:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (New Cl);
    find_handler_for P OutOfMemory ((C, M, pc)#cs) = cs';
    ek = (\<lambda>(h,stk,loc). new_Addr h = None)\<^sub>\<surd> \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, pc)#cs,\<lfloor>(cs',True)\<rfloor> _)"

| JCFG_New_Exc_Update:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (New Cl);
    find_handler_for P OutOfMemory ((C, M, pc)#cs) = (C', M', pc')#cs';
    ek = \<Up>(\<lambda>(h,stk,loc).
     (h,
      stk((length cs',(stkLength P C' M' pc') - 1) := Addr (addr_of_sys_xcpt OutOfMemory)),
      loc)
     ) \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>((C', M', pc')#cs', True)\<rfloor> _) -ek\<rightarrow> (_ (C', M', pc')#cs',None _)"

| JCFG_New_Exc_Exit:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (New Cl);
    find_handler_for P OutOfMemory ((C, M, pc)#cs) = [] \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>([], True)\<rfloor> _) -\<Up>id\<rightarrow> (_Exit_)"

| JCFG_Getfield_Normal_Pred:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Getfield Fd Cl);
    ek = (\<lambda>(h,stk,loc).  stk(length cs, stkLength P C M pc - 1) \<noteq> Null)\<^sub>\<surd> \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, pc)#cs,\<lfloor>((C, M, Suc pc)#cs, False)\<rfloor> _)"

| JCFG_Getfield_Normal_Update:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Getfield Fd Cl);
    ek = \<Up>(\<lambda>s. exec_instr (Getfield Fd Cl) P s (length cs) (stkLength P C M pc)
                          arbitrary arbitrary) \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>((C, M, Suc pc)#cs, False)\<rfloor> _) -ek\<rightarrow> (_ (C, M, Suc pc)#cs,None _)"

| JCFG_Getfield_Exc_Pred:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Getfield Fd Cl);
    find_handler_for P NullPointer ((C, M, pc)#cs) = cs';
    ek = (\<lambda>(h,stk,loc). stk(length cs, stkLength P C M pc - 1) = Null)\<^sub>\<surd> \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, pc)#cs,\<lfloor>(cs', True)\<rfloor> _)"

| JCFG_Getfield_Exc_Update:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Getfield Fd Cl);
    find_handler_for P NullPointer ((C, M, pc)#cs) = (C', M', pc')#cs';
    ek =  \<Up>(\<lambda>(h,stk,loc).
     (h,
      stk((length cs',(stkLength P C' M' pc') - 1) := Addr (addr_of_sys_xcpt NullPointer)),
      loc)
     ) \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>((C', M', pc')#cs', True)\<rfloor> _) -ek\<rightarrow> (_ (C', M', pc')#cs',None _)"

| JCFG_Getfield_Exc_Exit:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Getfield Fd Cl);
    find_handler_for P NullPointer ((C, M, pc)#cs) = [] \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>([], True)\<rfloor> _) -\<Up>id\<rightarrow> (_Exit_)"

| JCFG_Putfield_Normal_Pred:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Putfield Fd Cl);
    ek = (\<lambda>(h,stk,loc).  stk(length cs, stkLength P C M pc - 2) \<noteq> Null)\<^sub>\<surd> \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, pc)#cs,\<lfloor>((C, M, Suc pc)#cs, False)\<rfloor> _)"

| JCFG_Putfield_Normal_Update:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Putfield Fd Cl);
    ek = \<Up>(\<lambda>s. exec_instr (Putfield Fd Cl) P s (length cs) (stkLength P C M pc)
                          arbitrary arbitrary) \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>((C, M, Suc pc)#cs, False)\<rfloor> _) -ek\<rightarrow> (_ (C, M, Suc pc)#cs,None _)"

| JCFG_Putfield_Exc_Pred:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Putfield Fd Cl);
    find_handler_for P NullPointer ((C, M, pc)#cs) = cs';
    ek = (\<lambda>(h,stk,loc). stk(length cs, stkLength P C M pc - 2) = Null)\<^sub>\<surd> \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, pc)#cs,\<lfloor>(cs', True)\<rfloor> _)"

| JCFG_Putfield_Exc_Update:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Putfield Fd Cl);
    find_handler_for P NullPointer ((C, M, pc)#cs) = (C', M', pc')#cs';
    ek = \<Up>(\<lambda>(h,stk,loc).
     (h,
      stk((length cs',(stkLength P C' M' pc') - 1) := Addr (addr_of_sys_xcpt NullPointer)),
      loc)
     ) \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>((C', M', pc')#cs', True)\<rfloor> _) -ek\<rightarrow> (_ (C', M', pc')#cs',None _)"

| JCFG_Putfield_Exc_Exit:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Putfield Fd Cl);
    find_handler_for P NullPointer ((C, M, pc)#cs) = [] \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>([], True)\<rfloor> _) -\<Up>id\<rightarrow> (_Exit_)"

| JCFG_Checkcast_Normal_Pred:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Checkcast Cl);
    ek = (\<lambda>(h,stk,loc). cast_ok (P\<^bsub>wf\<^esub>) Cl h (stk(length cs, stkLength P C M pc - Suc 0)))\<^sub>\<surd> \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, Suc pc)#cs,None _)"

| JCFG_Checkcast_Exc_Pred:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Checkcast Cl);
    find_handler_for P ClassCast ((C, M, pc)#cs) = cs';
    ek = (\<lambda>(h,stk,loc). \<not> cast_ok (P\<^bsub>wf\<^esub>) Cl h (stk(length cs, stkLength P C M pc - Suc 0)))\<^sub>\<surd> \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, pc)#cs,\<lfloor>(cs', True)\<rfloor> _)"

| JCFG_Checkcast_Exc_Update:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Checkcast Cl);
    find_handler_for P ClassCast ((C, M, pc)#cs) = (C', M', pc')#cs';
    ek = \<Up>(\<lambda>(h,stk,loc).
     (h,
      stk((length cs',(stkLength P C' M' pc') - 1) := Addr (addr_of_sys_xcpt ClassCast)),
      loc)
     ) \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>((C', M', pc')#cs', True)\<rfloor> _) -ek\<rightarrow> (_ (C', M', pc')#cs',None _)"

| JCFG_Checkcast_Exc_Exit:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Checkcast Cl);
    find_handler_for P ClassCast ((C, M, pc)#cs) = [] \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>([], True)\<rfloor> _) -\<Up>id\<rightarrow> (_Exit_)"

| JCFG_Invoke_Normal_Pred:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Invoke M2 n);
    cd = length cs;
    stk_length = stkLength P C M pc;
    ek = (\<lambda>(h,stk,loc).
     stk(cd, stk_length - Suc n) \<noteq> Null \<and>
     fst(method (P\<^bsub>wf\<^esub>) (cname_of h (the_Addr(stk(cd, stk_length - Suc n)))) M2) = D
    )\<^sub>\<surd> \<rbrakk>
    \<Longrightarrow>
      prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, pc)#cs,\<lfloor>((D, M2, 0)#(C, M, pc)#cs, False)\<rfloor> _)"

| JCFG_Invoke_Normal_Update:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Invoke M2 n);
    stk_length = stkLength P C M pc;
    loc_length = locLength P D M2 0;
    ek = \<Up>(\<lambda>s. exec_instr (Invoke M2 n) P s (length cs) stk_length arbitrary loc_length)
   \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>((D, M2, 0)#(C, M, pc)#cs, False)\<rfloor> _) -ek\<rightarrow>
               (_ (D, M2, 0)#(C, M, pc)#cs,None _)"

| JCFG_Invoke_Exc_Pred:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Invoke m2 n);
    find_handler_for P NullPointer ((C, M, pc)#cs) = cs';
    ek = (\<lambda>(h,stk,loc). stk(length cs, stkLength P C M pc - Suc n) = Null)\<^sub>\<surd> \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, pc)#cs,\<lfloor>(cs', True)\<rfloor> _)"

| JCFG_Invoke_Exc_Update:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Invoke M2 n);
    find_handler_for P NullPointer ((C, M, pc)#cs) = (C', M', pc')#cs';
    ek = \<Up>(\<lambda>(h,stk,loc).
     (h,
      stk((length cs',(stkLength P C' M' pc') - 1) := Addr (addr_of_sys_xcpt NullPointer)),
      loc)
     )
   \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>((C', M', pc')#cs', True)\<rfloor> _) -ek\<rightarrow> (_ (C', M', pc')#cs',None _)"

| JCFG_Invoke_Exc_Exit:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (Invoke M2 n);
    find_handler_for P NullPointer ((C, M, pc)#cs) = [] \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>([], True)\<rfloor> _) -\<Up>id\<rightarrow> (_Exit_)"

| JCFG_Return_Update:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = Return;
    stk_length = stkLength P C M pc;
    r_stk_length = stkLength P C' M' (Suc pc');
    ek = \<Up>(\<lambda>s. exec_instr Return P s (Suc (length cs)) stk_length r_stk_length arbitrary) \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#(C', M', pc')#cs,None _) -ek\<rightarrow> (_ (C', M', Suc pc')#cs,None _)"

| JCFG_Goto_Update:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = Goto idx \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -\<Up>id\<rightarrow> (_ (C, M, nat (int pc + idx))#cs,None _)"

| JCFG_IfFalse_False:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (IfFalse b);
    b \<noteq> 1;
    ek = (\<lambda>(h,stk,loc). stk(length cs, stkLength P C M pc - 1) = Bool False)\<^sub>\<surd> \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, nat (int pc + b))#cs,None _)"

| JCFG_IfFalse_Next:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = (IfFalse b);
    ek = (\<lambda>(h,stk,loc). stk(length cs, stkLength P C M pc - 1) \<noteq> Bool False \<or> b = 1)\<^sub>\<surd> \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, Suc pc)#cs,None _)"

| JCFG_Throw_Pred:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = Throw;
    cd = length cs;
    stk_length = stkLength P C M pc;
    \<exists>Exc. find_handler_for P Exc ((C, M, pc)#cs) = cs';
    ek = (\<lambda>(h,stk,loc).
      (stk(length cs, stkLength P C M pc - 1) = Null \<and>
        find_handler_for P NullPointer ((C, M, pc)#cs) = cs') \<or>
      (stk(length cs, stkLength P C M pc - 1) \<noteq> Null \<and>
        find_handler_for P (cname_of h (the_Addr(stk(cd, stk_length - 1)))) ((C, M, pc)#cs) = cs')
    )\<^sub>\<surd> \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,None _) -ek\<rightarrow> (_ (C, M, pc)#cs,\<lfloor>(cs', True)\<rfloor> _)"

| JCFG_Throw_Update:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = Throw;
    ek = \<Up>(\<lambda>(h,stk,loc).
      (h,
       stk((length cs',(stkLength P C' M' pc') - 1) :=
         if (stk(length cs, stkLength P C M pc - 1) = Null) then
           Addr (addr_of_sys_xcpt NullPointer)
         else (stk(length cs, stkLength P C M pc - 1))),
       loc)
    ) \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>((C', M', pc')#cs', True)\<rfloor> _) -ek\<rightarrow> (_ (C', M', pc')#cs',None _)"

| JCFG_Throw_Exit:
  "\<lbrakk> prog = (P, C0, Main);
    (instrs_of (P\<^bsub>wf\<^esub>) C M) ! pc = Throw \<rbrakk>
    \<Longrightarrow> prog \<turnstile> (_ (C, M, pc)#cs,\<lfloor>([],True)\<rfloor> _) -\<Up>id\<rightarrow> (_Exit_)"


subsection \<open>CFG properties\<close>

lemma JVMCFG_Exit_no_sourcenode [dest]:
  assumes edge:"prog \<turnstile> (_Exit_) -et\<rightarrow> n'"
  shows "False"
proof -
  { fix n 
    have "\<lbrakk>prog \<turnstile> n -et\<rightarrow> n'; n = (_Exit_)\<rbrakk> \<Longrightarrow> False"
      by (auto elim!: JVM_CFG.cases)
  }
  with edge show ?thesis by fastforce
qed

lemma JVMCFG_Entry_no_targetnode [dest]:
  assumes edge:"prog \<turnstile> n -et\<rightarrow> (_Entry_)"
  shows "False"
proof -
  { fix n' have "\<lbrakk>prog \<turnstile> n -et\<rightarrow> n'; n' = (_Entry_)\<rbrakk> \<Longrightarrow> False"
      by (auto elim!: JVM_CFG.cases)
  }
  with edge show ?thesis by fastforce
qed

lemma JVMCFG_EntryD:
  "\<lbrakk>(P,C,M) \<turnstile> n -et\<rightarrow> n'; n = (_Entry_)\<rbrakk> 
  \<Longrightarrow> (n' = (_Exit_) \<and> et = (\<lambda>s. False)\<^sub>\<surd>) \<or> (n' = (_ [(C,M,0)],None _) \<and> et = (\<lambda>s. True)\<^sub>\<surd>)"
by (erule JVM_CFG.cases) simp_all

declare split_def [simp add]
declare find_handler_for.simps [simp del]

(* The following lemma explores many cases, it takes a little to prove *)
lemma JVMCFG_edge_det:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow> n'; prog \<turnstile> n -et'\<rightarrow> n'\<rbrakk> \<Longrightarrow> et = et'"
  by (erule JVM_CFG.cases, (erule JVM_CFG.cases, fastforce+)+)

declare split_def [simp del]
declare find_handler_for.simps [simp add]

end
