(*  Title:      JinjaThreads/JVM/JVMExecInstr.thy
    Author:     Cornelia Pusch, Gerwin Klein, Andreas Lochbihler
*)

section \<open>JVM Instruction Semantics\<close>

theory JVMExecInstr
imports
  JVMInstructions
  JVMHeap
  "../Common/ExternalCall"
begin

primrec extRet2JVM :: 
  "nat \<Rightarrow> 'heap \<Rightarrow> 'addr val list \<Rightarrow> 'addr val list \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> pc \<Rightarrow> 'addr frame list 
  \<Rightarrow> 'addr extCallRet \<Rightarrow> ('addr, 'heap) jvm_state"
where
  "extRet2JVM n h stk loc C M pc frs (RetVal v) = (None, h, (v # drop (Suc n) stk, loc, C, M, pc + 1) # frs)"
| "extRet2JVM n h stk loc C M pc frs (RetExc a) = (\<lfloor>a\<rfloor>, h, (stk, loc, C, M, pc) # frs)"
| "extRet2JVM n h stk loc C M pc frs RetStaySame = (None, h, (stk, loc, C, M, pc) # frs)"

lemma eq_extRet2JVM_conv [simp]:
  "(xcp, h', frs') = extRet2JVM n h stk loc C M pc frs va \<longleftrightarrow> 
   h' = h \<and> (case va of RetVal v \<Rightarrow> xcp = None \<and> frs' = (v # drop (Suc n) stk, loc, C, M, pc + 1) # frs
                      | RetExc a \<Rightarrow> xcp = \<lfloor>a\<rfloor> \<and> frs' = (stk, loc, C, M, pc) # frs
                      | RetStaySame \<Rightarrow> xcp = None \<and> frs' = (stk, loc, C, M, pc) # frs)"
by(cases va) auto

definition extNTA2JVM :: "'addr jvm_prog \<Rightarrow> (cname \<times> mname \<times> 'addr) \<Rightarrow> 'addr jvm_thread_state"
where "extNTA2JVM P \<equiv> (\<lambda>(C, M, a). let (D,M',Ts,meth) = method P C M; (mxs,mxl0,ins,xt) = the meth
                                   in (None, [([],Addr a # replicate mxl0 undefined_value, D, M, 0)]))"

abbreviation extTA2JVM :: 
  "'addr jvm_prog \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action"
where "extTA2JVM P \<equiv> convert_extTA (extNTA2JVM P)"

context JVM_heap_base begin

primrec exec_instr ::
  "'addr instr \<Rightarrow> 'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> 'addr val list \<Rightarrow> 'addr val list
  \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> pc \<Rightarrow> 'addr frame list \<Rightarrow>
    (('addr, 'thread_id, 'heap) jvm_thread_action \<times> ('addr, 'heap) jvm_state) set"
where
exec_instr_Load:
 "exec_instr (Load n) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
      {(\<epsilon>, (None, h, ((loc ! n) # stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))}"

| "exec_instr (Store n) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
      {(\<epsilon>, (None, h, (tl stk, loc[n:=hd stk], C\<^sub>0, M\<^sub>0, pc+1)#frs))}"

| exec_instr_Push:
 "exec_instr (Push v) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
      {(\<epsilon>, (None, h, (v # stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))}"

| exec_instr_New:
 "exec_instr (New C) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
  (let HA = allocate h (Class_type C)
   in if HA = {} then {(\<epsilon>, \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc) # frs)}
      else (\<lambda>(h', a). (\<lbrace>NewHeapElem a (Class_type C)\<rbrace>, None, h', (Addr a # stk, loc, C\<^sub>0, M\<^sub>0, pc + 1)#frs)) ` HA)"

| exec_instr_NewArray:
  "exec_instr (NewArray T) P t h stk loc C0 M0 pc frs =
  (let si = the_Intg (hd stk);
       i = nat (sint si)
   in (if si <s 0
       then {(\<epsilon>, \<lfloor>addr_of_sys_xcpt NegativeArraySize\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)}
        else let HA = allocate h (Array_type T i)
             in if HA = {} then {(\<epsilon>, \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)}
                else (\<lambda>(h', a). (\<lbrace>NewHeapElem a (Array_type T i)\<rbrace>, None, h', (Addr a # tl stk, loc, C0, M0, pc + 1) # frs)) ` HA))"

| exec_instr_ALoad:
  "exec_instr ALoad P t h stk loc C0 M0 pc frs =
   (let i = the_Intg (hd stk);
        va = hd (tl stk);
        a = the_Addr va;
        len = alen_of_htype (the (typeof_addr h a))
    in (if va = Null then {(\<epsilon>, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)}
        else if i <s 0 \<or> int len \<le> sint i then
             {(\<epsilon>, \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)}
        else {(\<lbrace>ReadMem a (ACell (nat (sint i))) v\<rbrace>, None, h, (v # tl (tl stk), loc, C0, M0, pc + 1) # frs) | v. 
              heap_read h a (ACell (nat (sint i))) v }))"

| exec_instr_AStore:
  "exec_instr AStore P t h stk loc C0 M0 pc frs =
  (let ve = hd stk;
       vi = hd (tl stk);
       va = hd (tl (tl stk))
   in (if va = Null then {(\<epsilon>, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)}
       else (let i = the_Intg vi;
                 idx = nat (sint i);
                 a = the_Addr va;
                 hT = the (typeof_addr h a);
                 T = ty_of_htype hT;
                 len = alen_of_htype hT;
                 U = the (typeof\<^bsub>h\<^esub> ve)
             in (if i <s 0 \<or> int len \<le> sint i then
                      {(\<epsilon>, \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)}
                 else if P \<turnstile> U \<le> the_Array T then 
                      {(\<lbrace>WriteMem a (ACell idx) ve\<rbrace>, None, h', (tl (tl (tl stk)), loc, C0, M0, pc+1) # frs)
                       | h'. heap_write h a (ACell idx) ve h'}
                 else {(\<epsilon>, (\<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>, h, (stk, loc, C0, M0, pc) # frs))}))))"

| exec_instr_ALength:
  "exec_instr ALength P t h stk loc C0 M0 pc frs =
   {(\<epsilon>, (let va = hd stk
         in if va = Null
            then (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
            else (None, h, (Intg (word_of_int (int (alen_of_htype (the (typeof_addr h (the_Addr va)))))) # tl stk, loc, C0, M0, pc+1) # frs)))}"

| "exec_instr (Getfield F C) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
   (let v = hd stk
    in if v = Null then {(\<epsilon>, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc) # frs)}
       else let a = the_Addr v
            in {(\<lbrace>ReadMem a (CField C F) v'\<rbrace>, None, h, (v' # (tl stk), loc, C\<^sub>0, M\<^sub>0, pc + 1) # frs) | v'.
                heap_read h a (CField C F) v'})"

| "exec_instr (Putfield F C) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
  (let v = hd stk;
       r = hd (tl stk)
   in if r = Null then {(\<epsilon>, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc) # frs)}
      else let a = the_Addr r
           in {(\<lbrace>WriteMem a (CField C F) v\<rbrace>, None, h', (tl (tl stk), loc, C\<^sub>0, M\<^sub>0, pc + 1) # frs) | h'.
               heap_write h a (CField C F) v h'})"

| "exec_instr (CAS F C) P t h stk loc C0 M0 pc frs =
  (let v'' = hd stk; v' = hd (tl stk); v = hd (tl (tl stk))
   in if v = Null then {(\<epsilon>, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)}
      else let a = the_Addr v
           in {(\<lbrace>ReadMem a (CField C F) v', WriteMem a (CField C F) v''\<rbrace>, None, h', (Bool True # tl (tl (tl stk)), loc, C0, M0, pc + 1) # frs) | h' .
                heap_read h a (CField C F) v' \<and> heap_write h a (CField C F) v'' h'} \<union>
              {(\<lbrace>ReadMem a (CField C F) v''\<rbrace>, None, h, (Bool False # tl (tl (tl stk)), loc, C0, M0, pc + 1) # frs) | v''.
                heap_read h a (CField C F) v'' \<and> v'' \<noteq> v'})"

| "exec_instr (Checkcast T) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  {(\<epsilon>, let U = the (typeof\<^bsub>h\<^esub> (hd stk))
       in if P \<turnstile> U \<le> T then (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc + 1) # frs)
          else (\<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc) # frs))}"

| "exec_instr (Instanceof T) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  {(\<epsilon>, None, h, (Bool (hd stk \<noteq> Null \<and> P \<turnstile> the (typeof\<^bsub>h\<^esub> (hd stk)) \<le> T) # tl stk, loc, C\<^sub>0, M\<^sub>0, pc + 1) # frs)}"

| exec_instr_Invoke:
 "exec_instr (Invoke M n) P t h stk loc C0 M0 pc frs =
  (let ps = rev (take n stk);
       r = stk ! n;
       a = the_Addr r;
       T = the (typeof_addr h a)
   in (if r = Null then {(\<epsilon>, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)}
       else 
         let C = class_type_of T;
             (D,M',Ts,meth)= method P C M
         in case meth of 
               Native \<Rightarrow>
               {(extTA2JVM P ta, extRet2JVM n h' stk loc C0 M0 pc frs va) | ta va h'.
                (ta, va, h') \<in> red_external_aggr P t a M ps h}
            | \<lfloor>(mxs,mxl\<^sub>0,ins,xt)\<rfloor> \<Rightarrow>
              let f' = ([],[r]@ps@(replicate mxl\<^sub>0 undefined_value),D,M,0)
              in {(\<epsilon>, None, h, f' # (stk, loc, C0, M0, pc) # frs)}))"

| "exec_instr Return P t h stk\<^sub>0 loc\<^sub>0 C\<^sub>0 M\<^sub>0 pc frs =
  {(\<epsilon>, (if frs=[] then (None, h, []) else 
       let v = hd stk\<^sub>0; 
           (stk,loc,C,m,pc) = hd frs;
           n = length (fst (snd (method P C\<^sub>0 M\<^sub>0)))
       in (None, h, (v#(drop (n+1) stk),loc,C,m,pc+1)#tl frs)) )}"

| "exec_instr Pop P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
      {(\<epsilon>, (None, h, (tl stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs) )}"

| "exec_instr Dup P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
      {(\<epsilon>, (None, h, (hd stk # stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs) )}"

| "exec_instr Swap P t h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
      {(\<epsilon>, (None, h, (hd (tl stk) # hd stk # tl (tl stk), loc, C\<^sub>0, M\<^sub>0, pc+1)#frs) )}"

| "exec_instr (BinOpInstr bop) P t h stk loc C0 M0 pc frs =
  {(\<epsilon>, 
   case the (binop bop (hd (tl stk)) (hd stk)) of
     Inl v \<Rightarrow> (None, h, (v # tl (tl stk), loc, C0, M0, pc+1) # frs)
   | Inr a \<Rightarrow> (Some a, h, (stk, loc, C0, M0, pc) # frs))}"

| "exec_instr (IfFalse i) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  {(\<epsilon>, (let pc' = if hd stk = Bool False then nat(int pc+i) else pc+1
        in (None, h, (tl stk, loc, C\<^sub>0, M\<^sub>0, pc')#frs)) )}"

| exec_instr_Goto:
 "exec_instr (Goto i) P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
      {(\<epsilon>, (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, nat(int pc+i))#frs) )}"

| "exec_instr ThrowExc P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  {(\<epsilon>, (let xp' = if hd stk = Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else \<lfloor>the_Addr(hd stk)\<rfloor>
        in (xp', h, (stk, loc, C\<^sub>0, M\<^sub>0, pc)#frs)) )}"

| exec_instr_MEnter:
 "exec_instr MEnter P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  {let v = hd stk
   in if v = Null
      then (\<epsilon>, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc) # frs)
      else (\<lbrace>Lock\<rightarrow>the_Addr v, SyncLock (the_Addr v)\<rbrace>, None, h, (tl stk, loc, C\<^sub>0, M\<^sub>0, pc + 1) # frs)}"

| exec_instr_MExit:
 "exec_instr MExit P t h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (let v = hd stk
   in if v = Null
      then {(\<epsilon>, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc)#frs)}
      else {(\<lbrace>Unlock\<rightarrow>the_Addr v, SyncUnlock (the_Addr v)\<rbrace>, None, h, (tl stk, loc, C\<^sub>0, M\<^sub>0, pc + 1) # frs),
            (\<lbrace>UnlockFail\<rightarrow>the_Addr v\<rbrace>, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc) # frs)})"

end

end
