(*  Title:      HOL/MicroJava/JVM/JVMExecInstr.thy

    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

section \<open>JVM Instruction Semantics\<close>

theory JVMExecInstr
imports JVMInstructions JVMState "../Common/Exceptions"
begin

primrec
  exec_instr :: "[instr, jvm_prog, heap, val list, val list,
                  cname, mname, pc, frame list] => jvm_state"
where
exec_instr_Load:
 "exec_instr (Load n) P h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
      (None, h, ((loc ! n) # stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs)"

| "exec_instr (Store n) P h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
      (None, h, (tl stk, loc[n:=hd stk], C\<^sub>0, M\<^sub>0, pc+1)#frs)"

| exec_instr_Push:
 "exec_instr (Push v) P h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
      (None, h, (v # stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs)"

| exec_instr_New:
 "exec_instr (New C) P h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
  (case new_Addr h of
    None \<Rightarrow>   (Some (addr_of_sys_xcpt OutOfMemory), h, (stk, loc, C\<^sub>0, M\<^sub>0, pc)#frs)
  | Some a \<Rightarrow> (None, h(a\<mapsto>blank P C), (Addr a#stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))"

| "exec_instr (Getfield F C) P h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
  (let v      = hd stk;
       xp'    = if v=Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else None;
       (D,fs) = the(h(the_Addr v))
   in (xp', h, (the(fs(F,C))#(tl stk), loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))"

| "exec_instr (Putfield F C) P h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
  (let v    = hd stk;
       r    = hd (tl stk);
       xp'  = if r=Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else None;
       a    = the_Addr r;
       (D,fs) = the (h a);
       h'  = h(a \<mapsto> (D, fs((F,C) \<mapsto> v)))
   in (xp', h', (tl (tl stk), loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))"

| "exec_instr (Checkcast C) P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (let v   = hd stk;
       xp' = if \<not>cast_ok P C h v then \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor> else None
   in (xp', h, (stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))"

| exec_instr_Invoke:
 "exec_instr (Invoke M n) P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (let ps  = take n stk;
       r   = stk!n;
       xp' = if r=Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else None;
       C   = fst(the(h(the_Addr r)));
       (D,M',Ts,mxs,mxl\<^sub>0,ins,xt)= method P C M;
       f'  = ([],[r]@(rev ps)@(replicate mxl\<^sub>0 undefined),D,M,0)
   in (xp', h, f'#(stk, loc, C\<^sub>0, M\<^sub>0, pc)#frs))" 

| "exec_instr Return P h stk\<^sub>0 loc\<^sub>0 C\<^sub>0 M\<^sub>0 pc frs =
  (if frs=[] then (None, h, []) else 
   let v = hd stk\<^sub>0; 
       (stk,loc,C,m,pc) = hd frs;
       n = length (fst (snd (method P C\<^sub>0 M\<^sub>0)))
   in (None, h, (v#(drop (n+1) stk),loc,C,m,pc+1)#tl frs))"

| "exec_instr Pop P h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
      (None, h, (tl stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs)"

| "exec_instr IAdd P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (let i\<^sub>2 = the_Intg (hd stk);
       i\<^sub>1 = the_Intg (hd (tl stk))
   in (None, h, (Intg (i\<^sub>1+i\<^sub>2)#(tl (tl stk)), loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))"

| "exec_instr (IfFalse i) P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (let pc' = if hd stk = Bool False then nat(int pc+i) else pc+1
   in (None, h, (tl stk, loc, C\<^sub>0, M\<^sub>0, pc')#frs))"

| "exec_instr CmpEq P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (let v\<^sub>2 = hd stk;
       v\<^sub>1 = hd (tl stk)
   in (None, h, (Bool (v\<^sub>1=v\<^sub>2) # tl (tl stk), loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))"

| exec_instr_Goto:
 "exec_instr (Goto i) P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
      (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, nat(int pc+i))#frs)"

| "exec_instr Throw P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (let xp' = if hd stk = Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else \<lfloor>the_Addr(hd stk)\<rfloor>
   in (xp', h, (stk, loc, C\<^sub>0, M\<^sub>0, pc)#frs))"


lemma exec_instr_Store:
  "exec_instr (Store n) P h (v#stk) loc C\<^sub>0 M\<^sub>0 pc frs = 
  (None, h, (stk, loc[n:=v], C\<^sub>0, M\<^sub>0, pc+1)#frs)" 
  by simp

lemma exec_instr_Getfield:
 "exec_instr (Getfield F C) P h (v#stk) loc C\<^sub>0 M\<^sub>0 pc frs = 
  (let xp'    = if v=Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else None;
       (D,fs) = the(h(the_Addr v))
   in (xp', h, (the(fs(F,C))#stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))"
  by simp

lemma exec_instr_Putfield:
 "exec_instr (Putfield F C) P h (v#r#stk) loc C\<^sub>0 M\<^sub>0 pc frs = 
  (let xp'  = if r=Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else None;
       a    = the_Addr r;
       (D,fs) = the (h a);
       h'  = h(a \<mapsto> (D, fs((F,C) \<mapsto> v)))
   in (xp', h', (stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))"
  by simp

lemma exec_instr_Checkcast:
 "exec_instr (Checkcast C) P h (v#stk) loc C\<^sub>0 M\<^sub>0 pc frs =
  (let xp' = if \<not>cast_ok P C h v then \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor> else None
   in (xp', h, (v#stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs))"
  by simp

lemma exec_instr_Return:
 "exec_instr Return P h (v#stk\<^sub>0) loc\<^sub>0 C\<^sub>0 M\<^sub>0 pc frs =
  (if frs=[] then (None, h, []) else 
   let (stk,loc,C,m,pc) = hd frs;
       n = length (fst (snd (method P C\<^sub>0 M\<^sub>0)))
   in (None, h, (v#(drop (n+1) stk),loc,C,m,pc+1)#tl frs))"
  by simp

lemma exec_instr_IPop:
 "exec_instr Pop P h (v#stk) loc C\<^sub>0 M\<^sub>0 pc frs = 
      (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs)"
  by simp

lemma exec_instr_IAdd:
 "exec_instr IAdd P h (Intg i\<^sub>2 # Intg i\<^sub>1 # stk) loc C\<^sub>0 M\<^sub>0 pc frs =
      (None, h, (Intg (i\<^sub>1+i\<^sub>2)#stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs)"
  by simp

lemma exec_instr_IfFalse:
 "exec_instr (IfFalse i) P h (v#stk) loc C\<^sub>0 M\<^sub>0 pc frs =
  (let pc' = if v = Bool False then nat(int pc+i) else pc+1
   in (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc')#frs))"
  by simp

lemma exec_instr_CmpEq:
 "exec_instr CmpEq P h (v\<^sub>2#v\<^sub>1#stk) loc C\<^sub>0 M\<^sub>0 pc frs =
  (None, h, (Bool (v\<^sub>1=v\<^sub>2) # stk, loc, C\<^sub>0, M\<^sub>0, pc+1)#frs)"
  by simp

lemma exec_instr_Throw:
 "exec_instr Throw P h (v#stk) loc C\<^sub>0 M\<^sub>0 pc frs =
  (let xp' = if v = Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else \<lfloor>the_Addr v\<rfloor>
   in (xp', h, (v#stk, loc, C\<^sub>0, M\<^sub>0, pc)#frs))"
  by simp

end
