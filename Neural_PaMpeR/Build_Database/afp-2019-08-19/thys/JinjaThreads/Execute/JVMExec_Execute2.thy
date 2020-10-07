(*  Title:      JinjaThreads/Execute/JVMExec_Execute2.thy
    Author:     Andreas Lochbihler
*)

section \<open>An optimized JVM\<close>

theory JVMExec_Execute2
imports
  "../BV/BVNoTypeError"
  ExternalCall_Execute
begin

text \<open>
  This JVM must lookup the method declaration of the top call frame at every step to find the next instruction.
  It is more efficient to refine it such that the instruction list and the exception table are
  cached in the call frame. Even further, this theory adds keeps track of @{term "drop pc ins"}, 
  whose head is the next instruction to execute. 
\<close>

locale JVM_heap_execute = heap_execute +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id" 
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr" 
  and spurious_wakeups :: bool
  and empty_heap :: "'heap" 
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<Rightarrow> htype option" 
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val set" 
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap set"

sublocale JVM_heap_execute < execute: JVM_heap_base
  addr2thread_id thread_id2addr 
  spurious_wakeups
  empty_heap allocate typeof_addr
  "\<lambda>h a ad v. v \<in> heap_read h a ad" "\<lambda>h a ad v h'. h' \<in> heap_write h a ad v"
.

type_synonym
  'addr frame' = "('addr instr list \<times> 'addr instr list \<times> ex_table) \<times> 'addr val list \<times> 'addr val list \<times> cname \<times> mname \<times> pc"

type_synonym
  ('addr, 'heap) jvm_state' = "'addr option \<times> 'heap \<times> 'addr frame' list"  

type_synonym
  'addr jvm_thread_state' = "'addr option \<times> 'addr frame' list"

type_synonym
  ('addr, 'thread_id, 'heap) jvm_thread_action' = "('addr, 'thread_id, 'addr jvm_thread_state','heap) Jinja_thread_action"

type_synonym
  ('addr, 'thread_id, 'heap) jvm_ta_state' = "('addr, 'thread_id, 'heap) jvm_thread_action' \<times> ('addr, 'heap) jvm_state'"

fun frame'_of_frame :: "'addr jvm_prog \<Rightarrow> 'addr frame \<Rightarrow> 'addr frame'"
where
  "frame'_of_frame P (stk, loc, C, M, pc) = 
  ((drop pc (instrs_of P C M), instrs_of P C M, ex_table_of P C M), stk, loc, C, M, pc)"

fun jvm_state'_of_jvm_state :: "'addr jvm_prog \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> ('addr, 'heap) jvm_state'"
where "jvm_state'_of_jvm_state P (xcp, h, frs) = (xcp, h, map (frame'_of_frame P) frs)"

fun jvm_thread_state'_of_jvm_thread_state :: "'addr jvm_prog \<Rightarrow> 'addr jvm_thread_state \<Rightarrow> 'addr jvm_thread_state'"
where
  "jvm_thread_state'_of_jvm_thread_state P (xcp, frs) = (xcp, map (frame'_of_frame P) frs)"

definition jvm_thread_action'_of_jvm_thread_action :: 
  "'addr jvm_prog \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action'"
where
  "jvm_thread_action'_of_jvm_thread_action P = convert_extTA (jvm_thread_state'_of_jvm_thread_state P)"

fun jvm_ta_state'_of_jvm_ta_state :: 
  "'addr jvm_prog \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_ta_state \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_ta_state'"
where
  "jvm_ta_state'_of_jvm_ta_state P (ta, s) = (jvm_thread_action'_of_jvm_thread_action P ta, jvm_state'_of_jvm_state P s)"

abbreviation (input) frame_of_frame' :: "'addr frame' \<Rightarrow> 'addr frame"
where "frame_of_frame' \<equiv> snd"

definition jvm_state_of_jvm_state' :: "('addr, 'heap) jvm_state' \<Rightarrow> ('addr, 'heap) jvm_state"
where [simp]: 
  "jvm_state_of_jvm_state' = map_prod id (map_prod id (map frame_of_frame'))"

definition jvm_thread_state_of_jvm_thread_state' :: "'addr jvm_thread_state' \<Rightarrow> 'addr jvm_thread_state"
where [simp]:
  "jvm_thread_state_of_jvm_thread_state' = map_prod id (map frame_of_frame')"

definition jvm_thread_action_of_jvm_thread_action' ::
  "('addr, 'thread_id, 'heap) jvm_thread_action' \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action"
where [simp]:
  "jvm_thread_action_of_jvm_thread_action' = convert_extTA jvm_thread_state_of_jvm_thread_state'"

definition jvm_ta_state_of_jvm_ta_state' ::
  "('addr, 'thread_id, 'heap) jvm_ta_state' \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_ta_state"
where [simp]:
  "jvm_ta_state_of_jvm_ta_state' = map_prod jvm_thread_action_of_jvm_thread_action' jvm_state_of_jvm_state'"

fun frame'_ok :: "'addr jvm_prog \<Rightarrow> 'addr frame' \<Rightarrow> bool"
where 
  "frame'_ok P ((ins', insxt), stk, loc, C, M, pc) \<longleftrightarrow> 
  ins' = drop pc (instrs_of P C M) \<and> insxt = snd (snd (the (snd (snd (snd (method P C M))))))"

lemma frame'_ok_frame'_of_frame [iff]: 
  "frame'_ok P (frame'_of_frame P f)"
by(cases f)(simp)

lemma frames'_ok_inverse [simp]:
  "\<forall>x\<in>set frs. frame'_ok P x \<Longrightarrow> map (frame'_of_frame P \<circ> frame_of_frame') frs = frs"
by(rule map_idI) auto

fun jvm_state'_ok :: "'addr jvm_prog \<Rightarrow> ('addr, 'heap) jvm_state' \<Rightarrow> bool"
where "jvm_state'_ok P (xcp, h, frs) = (\<forall>f \<in> set frs. frame'_ok P f)"

lemma jvm_state'_ok_jvm_state'_of_jvm_state [iff]:
  "jvm_state'_ok P (jvm_state'_of_jvm_state P s)"
by(cases s) simp

fun jvm_thread_state'_ok :: "'addr jvm_prog \<Rightarrow> 'addr jvm_thread_state' \<Rightarrow> bool"
where "jvm_thread_state'_ok P (xcp, frs) \<longleftrightarrow> (\<forall>f \<in> set frs. frame'_ok P f)"

lemma jvm_thread_state'_ok_jvm_thread_state'_of_jvm_thread_state [iff]:
  "jvm_thread_state'_ok P (jvm_thread_state'_of_jvm_thread_state P s)"
by(cases s) simp

definition jvm_thread_action'_ok :: "'addr jvm_prog \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action' \<Rightarrow> bool"
where "jvm_thread_action'_ok P ta \<longleftrightarrow> (\<forall>nt \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>. \<forall>t x h. nt = NewThread t x h \<longrightarrow> jvm_thread_state'_ok P x)"

lemma jvm_thread_action'_ok_jvm_thread_action'_of_jvm_thread_action [iff]:
  "jvm_thread_action'_ok P (jvm_thread_action'_of_jvm_thread_action P ta)"
by(cases ta)(fastforce dest: sym simp add: jvm_thread_action'_ok_def jvm_thread_action'_of_jvm_thread_action_def)

lemma jvm_thread_action'_ok_\<epsilon> [simp]: "jvm_thread_action'_ok P \<epsilon>"
by(simp add: jvm_thread_action'_ok_def)

fun jvm_ta_state'_ok :: "'addr jvm_prog \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_ta_state' \<Rightarrow> bool"
where "jvm_ta_state'_ok P (ta, s) \<longleftrightarrow> jvm_thread_action'_ok P ta \<and> jvm_state'_ok P s"

lemma jvm_ta_state'_ok_jvm_ta_state'_of_jvm_ta_state [iff]:
  "jvm_ta_state'_ok P (jvm_ta_state'_of_jvm_ta_state P tas)"
by(cases tas)(simp)

lemma frame_of_frame'_inverse [simp]: "frame_of_frame' \<circ> frame'_of_frame P = id"
by(clarsimp simp add: fun_eq_iff)

lemma convert_new_thread_action_frame_of_frame'_inverse [simp]:
  "convert_new_thread_action (map_prod id (map frame_of_frame')) \<circ> convert_new_thread_action (jvm_thread_state'_of_jvm_thread_state P) = id"
by(auto intro!: convert_new_thread_action_eqI simp add: fun_eq_iff List.map.id)

primrec extRet2JVM' :: 
  "'addr instr list \<Rightarrow> 'addr instr list \<Rightarrow> ex_table 
  \<Rightarrow> nat \<Rightarrow> 'heap \<Rightarrow> 'addr val list \<Rightarrow> 'addr val list \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> pc \<Rightarrow> 'addr frame' list 
  \<Rightarrow> 'addr extCallRet \<Rightarrow> ('addr, 'heap) jvm_state'"
where
  "extRet2JVM' ins' ins xt n h stk loc C M pc frs (RetVal v) = (None, h, ((tl ins', ins, xt), v # drop (Suc n) stk, loc, C, M, pc + 1) # frs)"
| "extRet2JVM' ins' ins xt n h stk loc C M pc frs (RetExc a) = (\<lfloor>a\<rfloor>, h, ((ins', ins, xt), stk, loc, C, M, pc) # frs)"
| "extRet2JVM' ins' ins xt n h stk loc C M pc frs RetStaySame = (None, h, ((ins', ins, xt), stk, loc, C, M, pc) # frs)"

definition extNTA2JVM' :: "'addr jvm_prog \<Rightarrow> (cname \<times> mname \<times> 'addr) \<Rightarrow> 'addr jvm_thread_state'"
where "extNTA2JVM' P \<equiv> (\<lambda>(C, M, a). let (D,Ts,T,meth) = method P C M; (mxs,mxl0,ins,xt) = the meth
                                   in (None, [((ins, ins, xt), [],Addr a # replicate mxl0 undefined_value, D, M, 0)]))"

abbreviation extTA2JVM' :: 
  "'addr jvm_prog \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action'"
where "extTA2JVM' P \<equiv> convert_extTA (extNTA2JVM' P)"

lemma jvm_state'_ok_extRet2JVM' [simp]:
  assumes [simp]: "ins = instrs_of P C M" "xt = ex_table_of P C M" "\<forall>f \<in> set frs. frame'_ok P f"
  shows "jvm_state'_ok P (extRet2JVM' (drop pc ins) ins xt n h stk loc C M pc frs va)"
by(cases va)(simp_all add: drop_tl drop_Suc)

lemma jvm_state'_of_jvm_state_extRet2JVM [simp]:
  assumes [simp]: "ins = instrs_of P C M" "xt = ex_table_of P C M" "\<forall>f \<in> set frs. frame'_ok P f"
  shows 
  "jvm_state'_of_jvm_state P (extRet2JVM n h' stk loc C M pc (map frame_of_frame' frs) va) =
   extRet2JVM' (drop pc (instrs_of P C M)) ins xt n h' stk loc C M pc frs va"
by(cases va)(simp_all add: drop_tl drop_Suc)

lemma extRet2JVM'_extRet2JVM [simp]:
  "jvm_state_of_jvm_state' (extRet2JVM' ins' ins xt n h' stk loc C M pc frs va) =
   extRet2JVM n h' stk loc C M pc (map frame_of_frame' frs) va"
by(cases va) simp_all


lemma jvm_ta_state'_ok_inverse:
  assumes "jvm_ta_state'_ok P tas" 
  shows "jvm_ta_state_of_jvm_ta_state' tas \<in> A \<longleftrightarrow> tas \<in> jvm_ta_state'_of_jvm_ta_state P ` A"
using assms
apply(cases tas)
apply(fastforce simp add: o_def jvm_thread_action'_of_jvm_thread_action_def jvm_thread_action'_ok_def intro!: map_idI[symmetric] map_idI convert_new_thread_action_eqI dest: bspec intro!: rev_image_eqI elim!: rev_iffD1[OF _ arg_cong[where f="\<lambda>x. x : A"]])
done


context JVM_heap_execute begin

primrec exec_instr ::
  "'addr instr list \<Rightarrow> 'addr instr list \<Rightarrow> ex_table 
  \<Rightarrow> 'addr instr \<Rightarrow> 'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> 'addr val list \<Rightarrow> 'addr val list
  \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> pc \<Rightarrow> 'addr frame' list 
  \<Rightarrow> (('addr, 'thread_id, 'heap) jvm_ta_state') set"
where
  "exec_instr ins' ins xt (Load n) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
   {(\<epsilon>, (None, h, ((tl ins', ins, xt), (loc ! n) # stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))}"
| "exec_instr ins' ins xt (Store n) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
   {(\<epsilon>, (None, h, ((tl ins', ins, xt), tl stk, loc[n:=hd stk], C\<^sub>0, M\<^sub>0, pc+1)#frs))}"
| "exec_instr ins' ins xt (Push v) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
   {(\<epsilon>, (None, h, ((tl ins', ins, xt), v # stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))}"
| "exec_instr ins' ins xt (New C) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
   (let HA = allocate h (Class_type C)
    in if HA = {} then {(\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt OutOfMemory\<rfloor>, h, ((ins', ins, xt), stk, loc, C\<^sub>0, M\<^sub>0, pc) # frs)}
       else do { (h', a) \<leftarrow> HA;
          {(\<lbrace>NewHeapElem a (Class_type C)\<rbrace>, None, h', ((tl ins', ins, xt), Addr a # stk, loc, C\<^sub>0, M\<^sub>0, pc + 1)#frs)}})"
| "exec_instr ins' ins xt (NewArray T) P t h stk loc C0 M0 pc frs =
   (let si = the_Intg (hd stk);
        i = nat (sint si)
     in if si <s 0
        then {(\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NegativeArraySize\<rfloor>, h, ((ins', ins, xt), stk, loc, C0, M0, pc) # frs)}
        else let HA = allocate h (Array_type T i) in
          if HA = {} then {(\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt OutOfMemory\<rfloor>, h, ((ins', ins, xt), stk, loc, C0, M0, pc) # frs)}
          else do { (h', a) \<leftarrow> HA;
                {(\<lbrace>NewHeapElem a (Array_type T i) \<rbrace>, None, h', ((tl ins', ins, xt), Addr a # tl stk, loc, C0, M0, pc + 1) # frs)}})"
| "exec_instr ins' ins xt ALoad P t h stk loc C0 M0 pc frs =
   (let va = hd (tl stk)
    in (if va = Null then {(\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, ((ins', ins, xt), stk, loc, C0, M0, pc) # frs)}
        else
          let i = the_Intg (hd stk);
              a = the_Addr va;
              len = alen_of_htype (the (typeof_addr h a))
          in if i <s 0 \<or> int len \<le> sint i then
               {(\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>, h, ((ins', ins, xt), stk, loc, C0, M0, pc) # frs)}
             else do {
               v \<leftarrow> heap_read h a (ACell (nat (sint i)));
               {(\<lbrace>ReadMem a (ACell (nat (sint i))) v\<rbrace>, None, h, ((tl ins', ins, xt), v # tl (tl stk), loc, C0, M0, pc + 1) # frs)}
             }))"
| "exec_instr ins' ins xt AStore P t h stk loc C0 M0 pc frs =
  (let ve = hd stk;
       vi = hd (tl stk);
       va = hd (tl (tl stk))
   in (if va = Null then {(\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, ((ins', ins, xt), stk, loc, C0, M0, pc) # frs)}
       else (let i = the_Intg vi;
                 idx = nat (sint i);
                 a = the_Addr va;
                 hT = the (typeof_addr h a);
                 T = ty_of_htype hT;
                 len = alen_of_htype hT;
                 U = the (execute.typeof_h h ve)
             in (if i <s 0 \<or> int len \<le> sint i then
                      {(\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>, h, ((ins', ins, xt), stk, loc, C0, M0, pc) # frs)}
                 else if P \<turnstile> U \<le> the_Array T then 
                      do {
                         h' \<leftarrow> heap_write h a (ACell idx) ve;
                         {(\<lbrace>WriteMem a (ACell idx) ve\<rbrace>, None, h', ((tl ins', ins, xt), tl (tl (tl stk)), loc, C0, M0, pc+1) # frs)}
                      }
                 else {(\<epsilon>, (\<lfloor>execute.addr_of_sys_xcpt ArrayStore\<rfloor>, h, ((ins', ins, xt), stk, loc, C0, M0, pc) # frs))}))))"
| "exec_instr ins' ins xt ALength P t h stk loc C0 M0 pc frs =
   {(\<epsilon>, (let va = hd stk
         in if va = Null
            then (\<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, ((ins', ins, xt), stk, loc, C0, M0, pc) # frs)
            else (None, h, ((tl ins', ins, xt), Intg (word_of_int (int (alen_of_htype (the (typeof_addr h (the_Addr va)))))) # tl stk, loc, C0, M0, pc+1) # frs)))}"
| "exec_instr ins' ins xt (Getfield F C) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
   (let v = hd stk
    in if v = Null then {(\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, ((ins', ins, xt), stk, loc, C\<^sub>0, M\<^sub>0, pc) # frs)}
       else let a = the_Addr v
            in do {
               v' \<leftarrow> heap_read h a (CField C F);
               {(\<lbrace>ReadMem a (CField C F) v'\<rbrace>, None, h, ((tl ins', ins, xt), v' # (tl stk), loc, C\<^sub>0, M\<^sub>0, pc + 1) # frs)}
            })"
| "exec_instr ins' ins xt (Putfield F C) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
  (let v = hd stk;
       r = hd (tl stk)
   in if r = Null then {(\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, ((ins', ins, xt), stk, loc, C\<^sub>0, M\<^sub>0, pc) # frs)}
      else let a = the_Addr r
           in do {
                h' \<leftarrow> heap_write h a (CField C F) v;
                {(\<lbrace>WriteMem a (CField C F) v\<rbrace>, None, h', ((tl ins', ins, xt), tl (tl stk), loc, C\<^sub>0, M\<^sub>0, pc + 1) # frs)}
              })"
| "exec_instr ins' ins xt (CAS F C) P t h stk loc C0 M0 pc frs =
  (let v'' = hd stk; v' = hd (tl stk); v = hd (tl (tl stk))
   in if v = Null then {(\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, ((ins', ins, xt), stk, loc, C0, M0, pc) # frs)}
      else let a = the_Addr v
           in do {
               v''' \<leftarrow> heap_read h a (CField C F);
               if v''' = v' then do {
                 h' \<leftarrow> heap_write h a (CField C F) v'';
                 {(\<lbrace>ReadMem a (CField C F) v', WriteMem a (CField C F) v''\<rbrace>, None, h', ((tl ins', ins, xt), Bool True # tl (tl (tl stk)), loc, C0, M0, pc + 1) # frs)}
               } else {(\<lbrace>ReadMem a (CField C F) v'''\<rbrace>, None, h, ((tl ins', ins, xt), Bool False # tl (tl (tl stk)), loc, C0, M0, pc + 1) # frs)}
             })"
| "exec_instr ins' ins xt (Checkcast T) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
   {(\<epsilon>, let U = the (typeof\<^bsub>h\<^esub> (hd stk))
        in if P \<turnstile> U \<le> T then (None, h, ((tl ins', ins, xt), stk, loc, C\<^sub>0, M\<^sub>0, pc + 1) # frs)
           else (\<lfloor>execute.addr_of_sys_xcpt ClassCast\<rfloor>, h, ((ins', ins, xt), stk, loc, C\<^sub>0, M\<^sub>0, pc) # frs))}"
| "exec_instr ins' ins xt (Instanceof T) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
   {(\<epsilon>, None, h, ((tl ins', ins, xt), Bool (hd stk \<noteq> Null \<and> P \<turnstile> the (typeof\<^bsub>h\<^esub> (hd stk)) \<le> T) # tl stk, loc, C\<^sub>0, M\<^sub>0, pc + 1) # frs)}"
| "exec_instr ins' ins xt (Invoke M n) P t h stk loc C0 M0 pc frs =
   (let r = stk ! n
    in (if r = Null then {(\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, ((ins', ins, xt), stk, loc, C0, M0, pc) # frs)}
        else (let ps = rev (take n stk);
                  a = the_Addr r;
                  T = the (typeof_addr h a);
                  (D,Ts,T,meth)= method P (class_type_of T) M
              in case meth of
                   Native \<Rightarrow> 
                      do {
                        (ta, va, h') \<leftarrow> red_external_aggr P t a M ps h;
                        {(extTA2JVM' P ta, extRet2JVM' ins' ins xt n h' stk loc C0 M0 pc frs va)}
                      }
                 | \<lfloor>(mxs,mxl\<^sub>0,ins'',xt'')\<rfloor> \<Rightarrow>
                       let f' = ((ins'', ins'', xt''), [],[r]@ps@(replicate mxl\<^sub>0 undefined_value),D,M,0)
                       in {(\<epsilon>, None, h, f' # ((ins', ins, xt), stk, loc, C0, M0, pc) # frs)})))"
| "exec_instr ins' ins xt Return P t h stk\<^sub>0 loc\<^sub>0 C\<^sub>0 M\<^sub>0 pc frs =
   {(\<epsilon>, (if frs=[] then (None, h, []) 
         else 
           let v = hd stk\<^sub>0; 
               ((ins', ins, xt), stk,loc,C,m,pc) = hd frs;
                n = length (fst (snd (method P C\<^sub>0 M\<^sub>0)))
           in (None, h, ((tl ins', ins, xt), v#(drop (n+1) stk),loc,C,m,pc+1)#tl frs)))}"
| "exec_instr ins' ins xt Pop P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
   {(\<epsilon>, (None, h, ((tl ins', ins, xt), tl stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))}"
| "exec_instr ins' ins xt Dup P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
   {(\<epsilon>, (None, h, ((tl ins', ins, xt), hd stk # stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))}"
| "exec_instr ins' ins xt Swap P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
   {(\<epsilon>, (None, h, ((tl ins', ins, xt), hd (tl stk) # hd stk # tl (tl stk), loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))}"
| "exec_instr ins' ins xt (BinOpInstr bop) P t h stk loc C0 M0 pc frs =
   {(\<epsilon>, 
     case the (execute.binop bop (hd (tl stk)) (hd stk)) of
       Inl v \<Rightarrow> (None, h, ((tl ins', ins, xt), v # tl (tl stk), loc, C0, M0, pc + 1) # frs)
     | Inr a \<Rightarrow> (Some a, h, ((ins', ins, xt), stk, loc, C0, M0, pc) # frs))}"
| "exec_instr ins' ins xt (IfFalse i) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
   {(\<epsilon>, (let pc' = if hd stk = Bool False then nat(int pc+i) else pc+1
         in (None, h, ((drop pc' ins, ins, xt), tl stk, loc, C\<^sub>0, M\<^sub>0, pc')#frs)))}"
| "exec_instr ins' ins xt (Goto i) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
   {let pc' = nat(int pc+i) 
    in (\<epsilon>, (None, h, ((drop pc' ins, ins, xt), stk, loc, C\<^sub>0, M\<^sub>0, pc')#frs))}"
| "exec_instr ins' ins xt ThrowExc P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
   {(\<epsilon>, (let xp' = if hd stk = Null then \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor> else \<lfloor>the_Addr(hd stk)\<rfloor>
         in (xp', h, ((ins', ins, xt), stk, loc, C\<^sub>0, M\<^sub>0, pc)#frs)))}"
| "exec_instr ins' ins xt MEnter P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
   {let v = hd stk
    in if v = Null
       then (\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, ((ins', ins, xt), stk, loc, C\<^sub>0, M\<^sub>0, pc) # frs)
       else (\<lbrace>Lock\<rightarrow>the_Addr v, SyncLock (the_Addr v)\<rbrace>, None, h, ((tl ins', ins, xt), tl stk, loc, C\<^sub>0, M\<^sub>0, pc + 1) # frs)}"
| "exec_instr ins' ins xt MExit P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (let v = hd stk
   in if v = Null
      then {(\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, ((ins', ins, xt), stk, loc, C\<^sub>0, M\<^sub>0, pc)#frs)}
      else {(\<lbrace>Unlock\<rightarrow>the_Addr v, SyncUnlock (the_Addr v)\<rbrace>, None, h, ((tl ins', ins, xt), tl stk, loc, C\<^sub>0, M\<^sub>0, pc + 1) # frs),
            (\<lbrace>UnlockFail\<rightarrow>the_Addr v\<rbrace>, \<lfloor>execute.addr_of_sys_xcpt IllegalMonitorState\<rfloor>, h, ((ins', ins, xt), stk, loc, C\<^sub>0, M\<^sub>0, pc) # frs)})"

fun exception_step :: "'addr jvm_prog \<Rightarrow> 'addr \<Rightarrow> 'heap \<Rightarrow> 'addr frame' \<Rightarrow> 'addr frame' list \<Rightarrow> ('addr, 'heap) jvm_state'"
where
  "exception_step P a h ((ins', ins, xt), stk, loc, C, M, pc) frs = 
   (case match_ex_table P (execute.cname_of h a) pc xt of
          None \<Rightarrow> (\<lfloor>a\<rfloor>, h, frs)
        | Some (pc', d) \<Rightarrow> (None, h, ((drop pc' ins, ins, xt), Addr a # drop (size stk - d) stk, loc, C, M, pc') # frs))"

fun exec :: "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'heap) jvm_state' \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_ta_state' set"
  where
  "exec P t (xcp, h, []) = {}"
| "exec P t (None, h, ((ins', ins, xt), stk, loc, C, M, pc) # frs) = 
   exec_instr ins' ins xt (hd ins') P t h stk loc C M pc frs"
| "exec P t (\<lfloor>a\<rfloor>, h, fr # frs) = {(\<epsilon>, exception_step P a h fr frs)}"

definition exec_1 ::
  "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'heap) jvm_state'
   \<Rightarrow> (('addr, 'thread_id, 'heap) jvm_thread_action' \<times> ('addr, 'heap) jvm_state') Predicate.pred"
where "exec_1 P t \<sigma> = pred_of_set (exec P t \<sigma>)"

lemma check_exec_instr_ok:
  assumes wf: "wf_prog wf_md P"
  and "execute.check_instr i P h stk loc C M pc (map frame_of_frame' frs)"
  and "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>m\<rfloor> in D"
  and "jvm_state'_ok P (None, h, ((ins', ins, xt), stk, loc, C, M, pc) # frs)"
  and "tas \<in> exec_instr ins' ins xt i P t h stk loc C M pc frs"
  shows "jvm_ta_state'_ok P tas"
proof -
  note [simp] = drop_Suc drop_tl split_beta jvm_thread_action'_ok_def has_method_def
  note [split] = if_split_asm sum.split
  from assms show ?thesis
  proof(cases i)
    case Return
    thus ?thesis using assms by(cases frs) auto
  next
    case Invoke
    thus ?thesis using assms 
      apply(cases m)
      apply(auto simp add: extNTA2JVM'_def dest: sees_method_idemp execute.red_external_aggr_new_thread_sub_thread sub_Thread_sees_run[OF wf])
       apply(drule execute.red_external_aggr_new_thread_sub_thread, clarsimp, clarsimp, assumption, clarsimp)
       apply(drule sub_Thread_sees_run[OF wf], clarsimp)
       apply(fastforce dest: sees_method_idemp)
      apply(drule execute.red_external_aggr_new_thread_sub_thread, clarsimp, clarsimp, assumption, clarsimp)
      apply(drule sub_Thread_sees_run[OF wf], clarsimp)
      apply(fastforce dest: sees_method_idemp)
      done
  next
    case Goto thus ?thesis using assms
      by(cases "m") simp
  next
    case IfFalse thus ?thesis using assms
      by(cases "m") simp
  qed(auto)
qed

lemma check_exec_instr_complete:
  assumes wf: "wf_prog wf_md P"
  and "execute.check_instr i P h stk loc C M pc (map frame_of_frame' frs)"
  and "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>m\<rfloor> in D"
  and "jvm_state'_ok P (None, h, ((ins', ins, xt), stk, loc, C, M, pc) # frs)"
  and "tas \<in> execute.exec_instr i P t h stk loc C M pc (map frame_of_frame' frs)"
  shows "jvm_ta_state'_of_jvm_ta_state P tas \<in> exec_instr ins' ins xt i P t h stk loc C M pc frs"
proof -
  note [simp] =
    drop_Suc drop_tl split_beta jvm_thread_action'_ok_def jvm_thread_action'_of_jvm_thread_action_def has_method_def
    ta_upd_simps map_tl
  note [split] = if_split_asm sum.split
  from assms show ?thesis
  proof(cases i)
    case Return thus ?thesis using assms by(cases frs) auto
  next
    case Goto thus ?thesis using assms
      by(cases "m") simp
  next
    case IfFalse thus ?thesis using assms
      by(cases "m") simp
  next
    case Invoke thus ?thesis using assms
      apply(cases "m")
      apply(auto intro!: rev_bexI convert_new_thread_action_eqI simp add: extNTA2JVM'_def extNTA2JVM_def dest: execute.red_external_aggr_new_thread_sub_thread sub_Thread_sees_run[OF wf] sees_method_idemp)
       apply(drule execute.red_external_aggr_new_thread_sub_thread, clarsimp, clarsimp, assumption, clarsimp)
       apply(drule sub_Thread_sees_run[OF wf], clarsimp)
       apply(fastforce dest: sees_method_idemp)
      apply(drule execute.red_external_aggr_new_thread_sub_thread, clarsimp, clarsimp, assumption, clarsimp)
      apply(drule sub_Thread_sees_run[OF wf], clarsimp)
      apply(fastforce dest: sees_method_idemp)
      done
  qed(auto 4 4)
qed

lemma check_exec_instr_refine:
  assumes wf: "wf_prog wf_md P"
  and "execute.check_instr i P h stk loc C M pc (map frame_of_frame' frs)"
  and "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>m\<rfloor> in D"
  and "jvm_state'_ok P (None, h, ((ins', ins, xt), stk, loc, C, M, pc) # frs)"
  and "tas \<in> exec_instr ins' ins xt i P t h stk loc C M pc frs"
  shows "tas \<in> jvm_ta_state'_of_jvm_ta_state P ` execute.exec_instr i P t h stk loc C M pc (map frame_of_frame' frs)"
proof -
  note [simp] =
    drop_Suc drop_tl split_beta jvm_thread_action'_ok_def jvm_thread_action'_of_jvm_thread_action_def has_method_def
    ta_upd_simps map_tl o_def
  note [split] = if_split_asm sum.split
  from assms have "jvm_ta_state_of_jvm_ta_state' tas \<in> execute.exec_instr i P t h stk loc C M pc (map frame_of_frame' frs)"
  proof (cases i)
    case Invoke thus ?thesis using assms
      by(fastforce simp add: extNTA2JVM'_def extNTA2JVM_def split_def extRet2JVM'_extRet2JVM[simplified])
  next
    case Return thus ?thesis using assms by(auto simp add: neq_Nil_conv)
  qed (auto cong del: image_cong_simp)
  also from assms have ok': "jvm_ta_state'_ok P tas" by(rule check_exec_instr_ok)
  hence "jvm_ta_state_of_jvm_ta_state' tas \<in> execute.exec_instr i P t h stk loc C M pc (map frame_of_frame' frs) \<longleftrightarrow>
    tas \<in> jvm_ta_state'_of_jvm_ta_state P ` execute.exec_instr i P t h stk loc C M pc (map frame_of_frame' frs)"
    by(rule jvm_ta_state'_ok_inverse)
  finally show ?thesis .
qed

lemma exception_step_ok:
  assumes "frame'_ok P fr" "\<forall>f\<in>set frs. frame'_ok P f"
  shows "jvm_state'_ok P (exception_step P a h fr frs)"
  and "exception_step P a h fr frs = jvm_state'_of_jvm_state P (execute.exception_step P a h (snd fr) (map frame_of_frame' frs))"
using assms
by(cases fr, case_tac "the (snd (snd (snd (method P d e))))", clarsimp)+

lemma exec_step_conv:
  assumes "wf_prog wf_md P"
  and "jvm_state'_ok P s"
  and "execute.check P (jvm_state_of_jvm_state' s)"
  shows "exec P t s = jvm_ta_state'_of_jvm_ta_state P ` execute.exec P t (jvm_state_of_jvm_state' s)"
using assms
apply(cases s)
apply(rename_tac xcp h frs)
apply(case_tac frs)
 apply(simp)
apply(case_tac xcp)
 prefer 2
 apply(simp add: jvm_thread_action'_of_jvm_thread_action_def exception_step_ok)
apply(clarsimp simp add: execute.check_def)
apply(rule equalityI)
 apply(clarsimp simp add: has_method_def)
 apply(erule (2) check_exec_instr_refine)
  apply fastforce
 apply(simp add: hd_drop_conv_nth)
apply(clarsimp simp add: has_method_def)
apply(drule (2) check_exec_instr_complete)
  apply fastforce
 apply(assumption)
apply(simp add: hd_drop_conv_nth)
done

lemma exec_step_ok:
  assumes "wf_prog wf_md P"
  and "jvm_state'_ok P s"
  and "execute.check P (jvm_state_of_jvm_state' s)"
  and "tas \<in> exec P t s"
  shows "jvm_ta_state'_ok P tas"
using assms
apply(cases s)
apply(rename_tac xcp h frs)
apply(case_tac frs)
 apply simp
apply(rename_tac fr frs')
apply(case_tac xcp)
 apply(clarsimp simp add: execute.check_def has_method_def)
 apply(erule (2) check_exec_instr_ok)
  apply fastforce
 apply(simp add: hd_drop_conv_nth)
apply(case_tac fr)
apply(rename_tac cache stk loc C M pc)
apply(case_tac "the (snd (snd (snd (method P C M))))")
apply auto
done

end


locale JVM_heap_execute_conf_read = JVM_heap_execute +
  execute: JVM_conf_read
    addr2thread_id thread_id2addr 
    spurious_wakeups
    empty_heap allocate typeof_addr 
    "\<lambda>h a ad v. v \<in> heap_read h a ad" "\<lambda>h a ad v h'. h' \<in> heap_write h a ad v"
  +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id" 
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr" 
  and spurious_wakeups :: bool
  and empty_heap :: "'heap" 
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set" 
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<Rightarrow> htype option" 
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val set" 
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap set"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "'addr jvm_prog"
begin

lemma exec_correct_state:
  assumes wt: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and correct: "execute.correct_state \<Phi> t (jvm_state_of_jvm_state' s)"
  and ok: "jvm_state'_ok P s"
  shows "exec P t s = jvm_ta_state'_of_jvm_ta_state P ` execute.exec P t (jvm_state_of_jvm_state' s)"
  (is ?thesis1)
  and "(ta, s') \<in> exec P t s \<Longrightarrow> execute.correct_state \<Phi> t (jvm_state_of_jvm_state' s')" (is "_ \<Longrightarrow> ?thesis2")
  and "tas \<in> exec P t s \<Longrightarrow> jvm_ta_state'_ok P tas"
proof -
  from wt obtain wf_md where wf: "wf_prog wf_md P" by(blast dest: wt_jvm_progD)
  from execute.no_type_error[OF wt correct]
  have check: "execute.check P (jvm_state_of_jvm_state' s)"
    by(simp add: execute.exec_d_def split: if_split_asm)
  with wf ok show eq: ?thesis1 by(rule exec_step_conv)

  { fix tas
    assume "tas \<in> exec P t s"
    with wf ok check show "jvm_ta_state'_ok P tas"
      by(rule exec_step_ok) }
  note this[of "(ta, s')"]
  moreover
  assume "(ta, s') \<in> exec P t s"
  moreover
  hence "(ta, s') \<in> jvm_ta_state'_of_jvm_ta_state P ` execute.exec P t (jvm_state_of_jvm_state' s)"
    unfolding eq by simp
  ultimately have "jvm_ta_state_of_jvm_ta_state' (ta, s') \<in> execute.exec P t (jvm_state_of_jvm_state' s)"
    using jvm_ta_state'_ok_inverse[of P "(ta, s')"] by blast
  hence "execute.exec_1 P t (jvm_state_of_jvm_state' s) (jvm_thread_action_of_jvm_thread_action' ta) (jvm_state_of_jvm_state' s')"
    by(simp add: execute.exec_1_iff)
  with wt correct show ?thesis2 by(rule execute.BV_correct_1)
qed

end

lemmas [code] = 
  JVM_heap_execute.exec_instr.simps
  JVM_heap_execute.exception_step.simps
  JVM_heap_execute.exec.simps
  JVM_heap_execute.exec_1_def

end
