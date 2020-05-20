(*  Title:      JinjaThreads/Compiler/Tau.thy
    Author:     Andreas Lochbihler
*)

section \<open>Unobservable steps for the JVM\<close>

theory JVMTau imports
  TypeComp
  "../JVM/JVMThreaded"
  "../Framework/FWLTS"
begin

declare nth_append [simp del]
declare Listn.lesub_list_impl_same_size[simp del]
declare listE_length [simp del]

declare match_ex_table_append_not_pcs[simp del]
  outside_pcs_not_matches_entry [simp del]
  outside_pcs_compxE2_not_matches_entry [simp del]
  outside_pcs_compxEs2_not_matches_entry [simp del]

context JVM_heap_base begin

primrec \<tau>instr :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr val list \<Rightarrow> 'addr instr \<Rightarrow> bool"
where
  "\<tau>instr P h stk (Load n) = True"
| "\<tau>instr P h stk (Store n) = True"
| "\<tau>instr P h stk (Push v) = True"
| "\<tau>instr P h stk (New C) = False"
| "\<tau>instr P h stk (NewArray T) = False"
| "\<tau>instr P h stk ALoad = False"
| "\<tau>instr P h stk AStore = False"
| "\<tau>instr P h stk ALength = False"
| "\<tau>instr P h stk (Getfield F D) = False"
| "\<tau>instr P h stk (Putfield F D) = False"
| "\<tau>instr P h stk (CAS F D) = False"
| "\<tau>instr P h stk (Checkcast T) = True"
| "\<tau>instr P h stk (Instanceof T) = True"
| "\<tau>instr P h stk (Invoke M n) = 
   (n < length stk \<and> 
    (stk ! n = Null \<or> 
     (\<forall>T Ts Tr D. typeof_addr h (the_Addr (stk ! n)) = \<lfloor>T\<rfloor> \<longrightarrow> P \<turnstile> class_type_of T sees M:Ts\<rightarrow>Tr = Native in D \<longrightarrow> \<tau>external_defs D M)))"
| "\<tau>instr P h stk Return = True"
| "\<tau>instr P h stk Pop = True"
| "\<tau>instr P h stk Dup = True"
| "\<tau>instr P h stk Swap = True"
| "\<tau>instr P h stk (BinOpInstr bop) = True"
| "\<tau>instr P h stk (Goto i) = True"
| "\<tau>instr P h stk (IfFalse i) = True" 
| "\<tau>instr P h stk ThrowExc = True"
| "\<tau>instr P h stk MEnter = False"
| "\<tau>instr P h stk MExit = False"

inductive \<tau>move2 :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr val list \<Rightarrow> 'addr expr1 \<Rightarrow> nat \<Rightarrow> 'addr option \<Rightarrow> bool"
  and \<tau>moves2 :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr val list \<Rightarrow> 'addr expr1 list \<Rightarrow> nat \<Rightarrow> 'addr option \<Rightarrow> bool"
for P :: "'m prog" and h :: 'heap and stk :: "'addr val list"
where
  \<tau>move2xcp: "pc < length (compE2 e) \<Longrightarrow> \<tau>move2 P h stk e pc \<lfloor>xcp\<rfloor>"

| \<tau>move2NewArray: "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (newA T\<lfloor>e\<rceil>) pc xcp"

| \<tau>move2Cast: "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (Cast T e) pc xcp"
| \<tau>move2CastRed: "\<tau>move2 P h stk (Cast T e) (length (compE2 e)) None"

| \<tau>move2InstanceOf: "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (e instanceof T) pc xcp"
| \<tau>move2InstanceOfRed: "\<tau>move2 P h stk (e instanceof T) (length (compE2 e)) None"

| \<tau>move2Val: "\<tau>move2 P h stk (Val v) 0 None"

| \<tau>move2BinOp1:
  "\<tau>move2 P h stk e1 pc xcp \<Longrightarrow> \<tau>move2 P h stk (e1\<guillemotleft>bop\<guillemotright>e2) pc xcp"
| \<tau>move2BinOp2:
  "\<tau>move2 P h stk e2 pc xcp \<Longrightarrow> \<tau>move2 P h stk (e1\<guillemotleft>bop\<guillemotright>e2) (length (compE2 e1) + pc) xcp"
| \<tau>move2BinOp:
  "\<tau>move2 P h stk (e1\<guillemotleft>bop\<guillemotright>e2) (length (compE2 e1) + length (compE2 e2)) None"

| \<tau>move2Var:
  "\<tau>move2 P h stk (Var V) 0 None"

| \<tau>move2LAss:
  "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (V:=e) pc xcp"
| \<tau>move2LAssRed1:
  "\<tau>move2 P h stk (V:=e) (length (compE2 e)) None"
| \<tau>move2LAssRed2:  "\<tau>move2 P h stk (V:=e) (Suc (length (compE2 e))) None"

| \<tau>move2AAcc1: "\<tau>move2 P h stk a pc xcp \<Longrightarrow> \<tau>move2 P h stk (a\<lfloor>i\<rceil>) pc xcp"
| \<tau>move2AAcc2: "\<tau>move2 P h stk i pc xcp \<Longrightarrow> \<tau>move2 P h stk (a\<lfloor>i\<rceil>) (length (compE2 a) + pc) xcp"

| \<tau>move2AAss1: "\<tau>move2 P h stk a pc xcp \<Longrightarrow> \<tau>move2 P h stk (a\<lfloor>i\<rceil> := e) pc xcp"
| \<tau>move2AAss2: "\<tau>move2 P h stk i pc xcp \<Longrightarrow> \<tau>move2 P h stk (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc) xcp"
| \<tau>move2AAss3: "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + pc) xcp"
| \<tau>move2AAssRed: "\<tau>move2 P h stk (a\<lfloor>i\<rceil> := e) (Suc (length (compE2 a) + length (compE2 i) + length (compE2 e))) None"

| \<tau>move2ALength: "\<tau>move2 P h stk a pc xcp \<Longrightarrow> \<tau>move2 P h stk (a\<bullet>length) pc xcp"

| \<tau>move2FAcc: "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (e\<bullet>F{D}) pc xcp"

| \<tau>move2FAss1: "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (e\<bullet>F{D} := e') pc xcp"
| \<tau>move2FAss2: "\<tau>move2 P h stk e' pc xcp \<Longrightarrow> \<tau>move2 P h stk (e\<bullet>F{D} := e') (length (compE2 e) + pc) xcp"
| \<tau>move2FAssRed: "\<tau>move2 P h stk (e\<bullet>F{D} := e') (Suc (length (compE2 e) + length (compE2 e'))) None"

| \<tau>move2CAS1: "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) pc xcp"
| \<tau>move2CAS2: "\<tau>move2 P h stk e' pc xcp \<Longrightarrow> \<tau>move2 P h stk (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) (length (compE2 e) + pc) xcp"
| \<tau>move2CAS3: "\<tau>move2 P h stk e'' pc xcp \<Longrightarrow> \<tau>move2 P h stk (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) (length (compE2 e) + length (compE2 e') + pc) xcp"

| \<tau>move2CallObj:
  "\<tau>move2 P h stk obj pc xcp \<Longrightarrow> \<tau>move2 P h stk (obj\<bullet>M(ps)) pc xcp"
| \<tau>move2CallParams:
  "\<tau>moves2 P h stk ps pc xcp \<Longrightarrow> \<tau>move2 P h stk (obj\<bullet>M(ps)) (length (compE2 obj) + pc) xcp"
| \<tau>move2Call:
  "\<lbrakk> length ps < length stk;
     stk ! length ps = Null \<or> 
     (\<forall>T Ts Tr D. typeof_addr h (the_Addr (stk ! length ps)) = \<lfloor>T\<rfloor> \<longrightarrow> P \<turnstile> class_type_of T sees M:Ts\<rightarrow>Tr = Native in D \<longrightarrow> \<tau>external_defs D M)\<rbrakk>
  \<Longrightarrow> \<tau>move2 P h stk (obj\<bullet>M(ps)) (length (compE2 obj) + length (compEs2 ps)) None"

| \<tau>move2BlockSome1:
  "\<tau>move2 P h stk {V:T=\<lfloor>v\<rfloor>; e} 0 None"
| \<tau>move2BlockSome2:
  "\<tau>move2 P h stk {V:T=\<lfloor>v\<rfloor>; e} (Suc 0) None"
| \<tau>move2BlockSome:
  "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk {V:T=\<lfloor>v\<rfloor>; e} (Suc (Suc pc)) xcp"
| \<tau>move2BlockNone:
  "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk {V:T=None; e} pc xcp"

| \<tau>move2Sync1:
  "\<tau>move2 P h stk o' pc xcp \<Longrightarrow> \<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) pc xcp"
| \<tau>move2Sync2:
  "\<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) (length (compE2 o')) None"
| \<tau>move2Sync3:
  "\<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) (Suc (length (compE2 o'))) None"
| \<tau>move2Sync4:
  "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) (Suc (Suc (Suc (length (compE2 o') + pc)))) xcp"
| \<tau>move2Sync5:
  "\<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) (Suc (Suc (Suc (length (compE2 o') + length (compE2 e))))) None"
| \<tau>move2Sync6:
  "\<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) (5 + length (compE2 o') + length (compE2 e)) None"
| \<tau>move2Sync7:
  "\<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) (6 + length (compE2 o') + length (compE2 e)) None"
| \<tau>move2Sync8:
  "\<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) (8 + length (compE2 o') + length (compE2 e)) None"

(* This is only because compE2 produces @{term "Goto 1"} for insync expressions. *)
| \<tau>move2InSync: "\<tau>move2 P h stk (insync\<^bsub>V\<^esub> (a) e) 0 None"

| \<tau>move2Seq1:
  "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (e;;e') pc xcp"
| \<tau>move2SeqRed:
  "\<tau>move2 P h stk (e;;e') (length (compE2 e)) None"
| \<tau>move2Seq2:
  "\<tau>move2 P h stk e' pc xcp \<Longrightarrow> \<tau>move2 P h stk (e;;e') (Suc (length (compE2 e) + pc)) xcp"

| \<tau>move2Cond:
  "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (if (e) e1 else e2) pc xcp"
| \<tau>move2CondRed:
  "\<tau>move2 P h stk (if (e) e1 else e2) (length (compE2 e)) None"
| \<tau>move2CondThen:
  "\<tau>move2 P h stk e1 pc xcp
  \<Longrightarrow> \<tau>move2 P h stk (if (e) e1 else e2) (Suc (length (compE2 e) + pc)) xcp"
| \<tau>move2CondThenExit:
  "\<tau>move2 P h stk (if (e) e1 else e2) (Suc (length (compE2 e) + length (compE2 e1))) None "
| \<tau>move2CondElse:
  "\<tau>move2 P h stk e2 pc xcp
  \<Longrightarrow> \<tau>move2 P h stk (if (e) e1 else e2) (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))) xcp "

| \<tau>move2While1:
  "\<tau>move2 P h stk c pc xcp \<Longrightarrow> \<tau>move2 P h stk (while (c) e) pc xcp"
| \<tau>move2While2:
  "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (while (c) e) (Suc (length (compE2 c) + pc)) xcp"
| \<tau>move2While3: \<comment> \<open>Jump back to condition\<close>
  "\<tau>move2 P h stk (while (c) e) (Suc (Suc (length (compE2 c) + length (compE2 e)))) None"
| \<tau>move2While4: \<comment> \<open>last instruction: Push Unit\<close>
  "\<tau>move2 P h stk (while (c) e) (Suc (Suc (Suc (length (compE2 c) + length (compE2 e))))) None"
| \<tau>move2While5: \<comment> \<open>IfFalse instruction\<close>
  "\<tau>move2 P h stk (while (c) e) (length (compE2 c)) None"
| \<tau>move2While6: \<comment> \<open>Pop instruction\<close>
  "\<tau>move2 P h stk (while (c) e) (Suc (length (compE2 c) + length (compE2 e))) None"

| \<tau>move2Throw1:
  "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (throw e) pc xcp"
| \<tau>move2Throw2:
  "\<tau>move2 P h stk (throw e) (length (compE2 e)) None"

| \<tau>move2Try1:
  "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h stk (try e catch(C V) e') pc xcp"
| \<tau>move2TryJump:
  "\<tau>move2 P h stk (try e catch(C V) e') (length (compE2 e)) None"
| \<tau>move2TryCatch2:
  "\<tau>move2 P h stk (try e catch(C V) e') (Suc (length (compE2 e))) None"
| \<tau>move2Try2:
  "\<tau>move2 P h stk {V:T=None; e'} pc xcp
  \<Longrightarrow> \<tau>move2 P h stk (try e catch(C V) e') (Suc (Suc (length (compE2 e) + pc))) xcp"

| \<tau>moves2Hd:
  "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>moves2 P h stk (e # es) pc xcp"
| \<tau>moves2Tl:
  "\<tau>moves2 P h stk es pc xcp \<Longrightarrow> \<tau>moves2 P h stk (e # es) (length (compE2 e) + pc) xcp"

inductive_cases \<tau>move2_cases:
  "\<tau>move2 P h stk (new C) pc xcp"
  "\<tau>move2 P h stk (newA T\<lfloor>e\<rceil>) pc xcp"
  "\<tau>move2 P h stk (Cast T e) pc xcp"
  "\<tau>move2 P h stk (e instanceof T) pc xcp"
  "\<tau>move2 P h stk (Val v) pc xcp"
  "\<tau>move2 P h stk (Var V) pc xcp"
  "\<tau>move2 P h stk (e1\<guillemotleft>bop\<guillemotright>e2) pc xcp"
  "\<tau>move2 P h stk (V := e) pc xcp"
  "\<tau>move2 P h stk (e1\<lfloor>e2\<rceil>) pc xcp"
  "\<tau>move2 P h stk (e1\<lfloor>e2\<rceil> := e3) pc xcp"
  "\<tau>move2 P h stk (e1\<bullet>length) pc xcp"
  "\<tau>move2 P h stk (e1\<bullet>F{D}) pc xcp"
  "\<tau>move2 P h stk (e1\<bullet>F{D} := e3) pc xcp"
  "\<tau>move2 P h stk (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) pc xcp"
  "\<tau>move2 P h stk (e\<bullet>M(ps)) pc xcp"
  "\<tau>move2 P h stk {V:T=vo; e} pc xcp"
  "\<tau>move2 P h stk (sync\<^bsub>V\<^esub> (e1) e2) pc xcp"
  "\<tau>move2 P h stk (e1;;e2) pc xcp"
  "\<tau>move2 P h stk (if (e1) e2 else e3) pc xcp"
  "\<tau>move2 P h stk (while (e1) e2) pc xcp"
  "\<tau>move2 P h stk (try e1 catch(C V) e2) pc xcp"
  "\<tau>move2 P h stk (throw e) pc xcp"

lemma \<tau>moves2xcp: "pc < length (compEs2 es) \<Longrightarrow> \<tau>moves2 P h stk es pc \<lfloor>xcp\<rfloor>"
proof(induct es arbitrary: pc)
  case Nil thus ?case by simp
next
  case (Cons e es)
  note IH = \<open>\<And>pc. pc < length (compEs2 es) \<Longrightarrow> \<tau>moves2 P h stk es pc \<lfloor>xcp\<rfloor>\<close>
  note pc = \<open>pc < length (compEs2 (e # es))\<close>
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    thus ?thesis by(auto intro: \<tau>moves2Hd \<tau>move2xcp)
  next
    case False
    with pc IH[of "pc - length (compE2 e)"]
    have "\<tau>moves2 P h stk es (pc - length (compE2 e)) \<lfloor>xcp\<rfloor>" by(simp)
    hence "\<tau>moves2 P h stk (e # es) (length (compE2 e) + (pc - length (compE2 e))) \<lfloor>xcp\<rfloor>"
      by(rule \<tau>moves2Tl)
    with False show ?thesis by simp
  qed
qed

lemma \<tau>move2_intros':
  shows \<tau>move2CastRed': "pc = length (compE2 e) \<Longrightarrow> \<tau>move2 P h stk (Cast T e) pc None"
  and \<tau>move2InstanceOfRed': "pc = length (compE2 e) \<Longrightarrow> \<tau>move2 P h stk (e instanceof T) pc None"
  and \<tau>move2BinOp2': "\<lbrakk> \<tau>move2 P h stk e2 pc xcp; pc' = length (compE2 e1) + pc \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk (e1\<guillemotleft>bop\<guillemotright>e2) pc' xcp"
  and \<tau>move2BinOp': "pc = length (compE2 e1) + length (compE2 e2) \<Longrightarrow> \<tau>move2 P h stk (e1\<guillemotleft>bop\<guillemotright>e2) pc None"
  and \<tau>move2LAssRed1': "pc = length (compE2 e) \<Longrightarrow> \<tau>move2 P h stk (V:=e) pc None"
  and \<tau>move2LAssRed2': "pc = Suc (length (compE2 e)) \<Longrightarrow> \<tau>move2 P h stk (V:=e) pc None"
  and \<tau>move2AAcc2': "\<lbrakk> \<tau>move2 P h stk i pc xcp; pc' = length (compE2 a) + pc \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk (a\<lfloor>i\<rceil>) pc' xcp"
  and \<tau>move2AAss2': "\<lbrakk> \<tau>move2 P h stk i pc xcp; pc' = length (compE2 a) + pc \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk (a\<lfloor>i\<rceil> := e) pc' xcp"
  and \<tau>move2AAss3': "\<lbrakk> \<tau>move2 P h stk e pc xcp; pc' = length (compE2 a) + length (compE2 i) + pc \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk (a\<lfloor>i\<rceil> := e) pc' xcp"
  and \<tau>move2AAssRed': "pc = Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)) \<Longrightarrow> \<tau>move2 P h stk (a\<lfloor>i\<rceil> := e) pc None"
  and \<tau>move2FAss2': "\<lbrakk> \<tau>move2 P h stk e' pc xcp; pc' = length (compE2 e) + pc \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk (e\<bullet>F{D} := e') pc' xcp"
  and \<tau>move2FAssRed': "pc = Suc (length (compE2 e) + length (compE2 e')) \<Longrightarrow> \<tau>move2 P h stk (e\<bullet>F{D} := e') pc None"
  and \<tau>move2CAS2': "\<lbrakk> \<tau>move2 P h stk e2 pc xcp; pc' = length (compE2 e1) + pc \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) pc' xcp"
  and \<tau>move2CAS3': "\<lbrakk> \<tau>move2 P h stk e3 pc xcp; pc' = length (compE2 e1) + length (compE2 e2) + pc \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) pc' xcp"
  and \<tau>move2CallParams': "\<lbrakk> \<tau>moves2 P h stk ps pc xcp; pc' = length (compE2 obj) + pc \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk (obj\<bullet>M(ps)) pc' xcp"
  and \<tau>move2Call': "\<lbrakk> pc = length (compE2 obj) + length (compEs2 ps); length ps < length stk; 
                     stk ! length ps = Null \<or> 
                     (\<forall>T Ts Tr D. typeof_addr h (the_Addr (stk ! length ps)) = \<lfloor>T\<rfloor> \<longrightarrow> P \<turnstile> class_type_of T sees M:Ts\<rightarrow>Tr = Native in D \<longrightarrow> \<tau>external_defs D M) \<rbrakk>
                   \<Longrightarrow> \<tau>move2 P h stk (obj\<bullet>M(ps)) pc None"
  and \<tau>move2BlockSome2: "pc = Suc 0 \<Longrightarrow> \<tau>move2 P h stk {V:T=\<lfloor>v\<rfloor>; e} pc None"
  and \<tau>move2BlockSome': "\<lbrakk> \<tau>move2 P h stk e pc xcp; pc' = Suc (Suc pc) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk {V:T=\<lfloor>v\<rfloor>; e} pc' xcp"
  and \<tau>move2Sync2': "pc = length (compE2 o') \<Longrightarrow> \<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) pc None"
  and \<tau>move2Sync3': "pc = Suc (length (compE2 o')) \<Longrightarrow> \<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) pc None"
  and \<tau>move2Sync4': "\<lbrakk> \<tau>move2 P h stk e pc xcp; pc' = Suc (Suc (Suc (length (compE2 o') + pc))) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) pc' xcp"
  and \<tau>move2Sync5': "pc = Suc (Suc (Suc (length (compE2 o') + length (compE2 e)))) \<Longrightarrow> \<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) pc None"
  and \<tau>move2Sync6': "pc = 5 + length (compE2 o') + length (compE2 e) \<Longrightarrow> \<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) pc None"
  and \<tau>move2Sync7': "pc = 6 + length (compE2 o') + length (compE2 e) \<Longrightarrow> \<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) pc None"
  and \<tau>move2Sync8': "pc = 8 + length (compE2 o') + length (compE2 e) \<Longrightarrow> \<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) pc None"
  and \<tau>move2SeqRed': "pc = length (compE2 e) \<Longrightarrow> \<tau>move2 P h stk (e;;e') pc None"
  and \<tau>move2Seq2': "\<lbrakk> \<tau>move2 P h stk e' pc xcp; pc' = Suc (length (compE2 e) + pc) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk (e;;e') pc' xcp"
  and \<tau>move2CondRed': "pc = length (compE2 e) \<Longrightarrow> \<tau>move2 P h stk (if (e) e1 else e2) pc None"
  and \<tau>move2CondThen': "\<lbrakk> \<tau>move2 P h stk e1 pc xcp; pc' = Suc (length (compE2 e) + pc) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk (if (e) e1 else e2) pc' xcp"
  and \<tau>move2CondThenExit': "pc = Suc (length (compE2 e) + length (compE2 e1)) \<Longrightarrow> \<tau>move2 P h stk (if (e) e1 else e2) pc None"
  and \<tau>move2CondElse': "\<lbrakk> \<tau>move2 P h stk e2 pc xcp; pc' = Suc (Suc (length (compE2 e) + length (compE2 e1) + pc)) \<rbrakk> 
                        \<Longrightarrow> \<tau>move2 P h stk (if (e) e1 else e2) pc' xcp"
  and \<tau>move2While2': "\<lbrakk> \<tau>move2 P h stk e pc xcp; pc' = Suc (length (compE2 c) + pc) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk (while (c) e) pc' xcp"
  and \<tau>move2While3': "pc = Suc (Suc (length (compE2 c) + length (compE2 e))) \<Longrightarrow> \<tau>move2 P h stk (while (c) e) pc None"
  and \<tau>move2While4': "pc = Suc (Suc (Suc (length (compE2 c) + length (compE2 e)))) \<Longrightarrow> \<tau>move2 P h stk (while (c) e) pc None"
  and \<tau>move2While5': "pc = length (compE2 c) \<Longrightarrow> \<tau>move2 P h stk (while (c) e) pc None"
  and \<tau>move2While6': "pc = Suc (length (compE2 c) + length (compE2 e)) \<Longrightarrow> \<tau>move2 P h stk (while (c) e) pc None"
  and \<tau>move2Throw2': "pc = length (compE2 e) \<Longrightarrow> \<tau>move2 P h stk (throw e) pc None"
  and \<tau>move2TryJump': "pc = length (compE2 e) \<Longrightarrow> \<tau>move2 P h stk (try e catch(C V) e') pc None"
  and \<tau>move2TryCatch2': "pc = Suc (length (compE2 e)) \<Longrightarrow> \<tau>move2 P h stk (try e catch(C V) e') pc None"
  and \<tau>move2Try2': "\<lbrakk> \<tau>move2 P h stk {V:T=None; e'} pc xcp; pc' = Suc (Suc (length (compE2 e) + pc)) \<rbrakk>
                    \<Longrightarrow> \<tau>move2 P h stk (try e catch(C V) e') pc' xcp"
  and \<tau>moves2Tl': "\<lbrakk> \<tau>moves2 P h stk es pc xcp; pc' = length (compE2 e) + pc \<rbrakk> \<Longrightarrow> \<tau>moves2 P h stk (e # es) pc' xcp"
apply(blast intro: \<tau>move2_\<tau>moves2.intros)+
done

lemma \<tau>move2_iff: "\<tau>move2 P h stk e pc xcp \<longleftrightarrow> pc < length (compE2 e) \<and> (xcp = None \<longrightarrow> \<tau>instr P h stk (compE2 e ! pc))" (is "?lhs1 \<longleftrightarrow> ?rhs1")
  and \<tau>moves2_iff: "\<tau>moves2 P h stk es pc xcp \<longleftrightarrow> pc < length (compEs2 es) \<and> (xcp = None \<longrightarrow> \<tau>instr P h stk (compEs2 es ! pc))" (is "?lhs2 \<longleftrightarrow> ?rhs2")
proof -
  have rhs1lhs1: "\<lbrakk> \<tau>instr P h stk (compE2 e ! pc); pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e pc None"
    and rhs2lhs2: "\<lbrakk> \<tau>instr P h stk (compEs2 es ! pc); pc < length (compEs2 es) \<rbrakk> \<Longrightarrow> \<tau>moves2 P h stk es pc None"
    apply(induct e and es arbitrary: pc and pc rule: compE2.induct compEs2.induct)
    apply(force intro: \<tau>move2_\<tau>moves2.intros \<tau>move2_intros' simp add: nth_append nth_Cons' not_less_eq split: if_split_asm)+
    done

  { assume "pc < length (compE2 e)" "xcp \<noteq> None"
    hence "\<tau>move2 P h stk e pc xcp" by(auto intro: \<tau>move2xcp) }
  with rhs1lhs1 have "?rhs1 \<Longrightarrow> ?lhs1" by(cases xcp) auto
  moreover {
    assume "pc < length (compEs2 es)" "xcp \<noteq> None"
    hence "\<tau>moves2 P h stk es pc xcp" by(auto intro: \<tau>moves2xcp) }
  with rhs2lhs2 have "?rhs2 \<Longrightarrow> ?lhs2" by(cases xcp) auto
  moreover have "?lhs1 \<Longrightarrow> ?rhs1" and "?lhs2 \<Longrightarrow> ?rhs2"
    by(induct rule: \<tau>move2_\<tau>moves2.inducts)(fastforce simp add: nth_append eval_nat_numeral)+
  ultimately show "?lhs1 \<longleftrightarrow> ?rhs1" "?lhs2 \<longleftrightarrow> ?rhs2" by blast+
qed

lemma \<tau>move2_pc_length_compE2: "\<tau>move2 P h stk e pc xcp \<Longrightarrow> pc < length (compE2 e)"
  and \<tau>moves2_pc_length_compEs2: "\<tau>moves2 P h stk es pc xcp \<Longrightarrow> pc < length (compEs2 es)"
by(simp_all add: \<tau>move2_iff \<tau>moves2_iff)

lemma \<tau>move2_pc_length_compE2_conv: "pc \<ge> length (compE2 e) \<Longrightarrow> \<not> \<tau>move2 P h stk e pc xcp"
by(auto dest: \<tau>move2_pc_length_compE2)

lemma \<tau>moves2_pc_length_compEs2_conv: "pc \<ge> length (compEs2 es) \<Longrightarrow> \<not> \<tau>moves2 P h stk es pc xcp"
by(auto dest: \<tau>moves2_pc_length_compEs2)

lemma \<tau>moves2_append [elim]:
  "\<tau>moves2 P h stk es pc xcp \<Longrightarrow> \<tau>moves2 P h stk (es @ es') pc xcp"
by(auto simp add: \<tau>moves2_iff nth_append)

lemma append_\<tau>moves2:
  "\<tau>moves2 P h stk es pc xcp \<Longrightarrow> \<tau>moves2 P h stk (es' @ es) (length (compEs2 es') + pc) xcp"
by(simp add: \<tau>moves2_iff)

lemma [dest]:
  shows \<tau>move2_NewArrayD: "\<lbrakk> \<tau>move2 P h stk (newA T\<lfloor>e\<rceil>) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e pc xcp"
  and \<tau>move2_CastD: "\<lbrakk> \<tau>move2 P h stk (Cast T e) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e pc xcp"
  and \<tau>move2_InstanceOfD: "\<lbrakk> \<tau>move2 P h stk (e instanceof T) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e pc xcp"
  and \<tau>move2_BinOp1D: "\<lbrakk> \<tau>move2 P h stk (e1 \<guillemotleft>bop\<guillemotright> e2) pc' xcp'; pc' < length (compE2 e1) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e1 pc' xcp'"
  and \<tau>move2_BinOp2D:
  "\<lbrakk> \<tau>move2 P h stk (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1) + pc') xcp'; pc' < length (compE2 e2) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e2 pc' xcp'"
  and \<tau>move2_LAssD: "\<lbrakk> \<tau>move2 P h stk (V := e) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e pc xcp"
  and \<tau>move2_AAccD1: "\<lbrakk> \<tau>move2 P h stk (a\<lfloor>i\<rceil>) pc xcp; pc < length (compE2 a) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk a pc xcp"
  and \<tau>move2_AAccD2: "\<lbrakk> \<tau>move2 P h stk (a\<lfloor>i\<rceil>) (length (compE2 a) + pc) xcp; pc < length (compE2 i) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk i pc xcp"
  and \<tau>move2_AAssD1: "\<lbrakk> \<tau>move2 P h stk (a\<lfloor>i\<rceil> := e) pc xcp; pc < length (compE2 a) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk a pc xcp"
  and \<tau>move2_AAssD2: "\<lbrakk> \<tau>move2 P h stk (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc) xcp; pc < length (compE2 i) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk i pc xcp"
  and \<tau>move2_AAssD3:
  "\<lbrakk> \<tau>move2 P h stk (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + pc) xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e pc xcp"
  and \<tau>move2_ALengthD: "\<lbrakk> \<tau>move2 P h stk (a\<bullet>length) pc xcp; pc < length (compE2 a) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk a pc xcp"
  and \<tau>move2_FAccD: "\<lbrakk> \<tau>move2 P h stk (e\<bullet>F{D}) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e pc xcp"
  and \<tau>move2_FAssD1: "\<lbrakk> \<tau>move2 P h stk (e\<bullet>F{D} := e') pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e pc xcp"
  and \<tau>move2_FAssD2: "\<lbrakk> \<tau>move2 P h stk (e\<bullet>F{D} := e') (length (compE2 e) + pc) xcp; pc < length (compE2 e') \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e' pc xcp"
  and \<tau>move2_CASD1: "\<lbrakk> \<tau>move2 P h stk (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) pc xcp; pc < length (compE2 e1) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e1 pc xcp"
  and \<tau>move2_CASD2: "\<lbrakk> \<tau>move2 P h stk (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) (length (compE2 e1) + pc) xcp; pc < length (compE2 e2) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e2 pc xcp"
  and \<tau>move2_CASD3:
  "\<lbrakk> \<tau>move2 P h stk (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) (length (compE2 e1) + length (compE2 e2) + pc) xcp; pc < length (compE2 e3) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e3 pc xcp"
  and \<tau>move2_CallObjD: "\<lbrakk> \<tau>move2 P h stk (e\<bullet>M(es)) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e pc xcp"
  and \<tau>move2_BlockNoneD: "\<tau>move2 P h stk {V:T=None; e} pc xcp \<Longrightarrow> \<tau>move2 P h stk e pc xcp"
  and \<tau>move2_BlockSomeD: "\<tau>move2 P h stk {V:T=\<lfloor>v\<rfloor>; e} (Suc (Suc pc)) xcp \<Longrightarrow> \<tau>move2 P h stk e pc xcp"
  and \<tau>move2_sync1D: "\<lbrakk> \<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) pc xcp; pc < length (compE2 o') \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk o' pc xcp"
  and \<tau>move2_sync2D:
  "\<lbrakk> \<tau>move2 P h stk (sync\<^bsub>V\<^esub> (o') e) (Suc (Suc (Suc (length (compE2 o') + pc)))) xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e pc xcp"
  and \<tau>move2_Seq1D: "\<lbrakk> \<tau>move2 P h stk (e1;; e2) pc xcp; pc < length (compE2 e1) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e1 pc xcp"
  and \<tau>move2_Seq2D: "\<tau>move2 P h stk (e1;; e2) (Suc (length (compE2 e1) + pc')) xcp' \<Longrightarrow> \<tau>move2 P h stk e2 pc' xcp'"
  and \<tau>move2_IfCondD: "\<lbrakk> \<tau>move2 P h stk (if (e) e1 else e2) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e pc xcp"
  and \<tau>move2_IfThenD:
  "\<lbrakk> \<tau>move2 P h stk (if (e) e1 else e2) (Suc (length (compE2 e) + pc')) xcp'; pc' < length (compE2 e1) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e1 pc' xcp'"
  and \<tau>move2_IfElseD:
  "\<tau>move2 P h stk (if (e) e1 else e2) (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc'))) xcp' \<Longrightarrow> \<tau>move2 P h stk e2 pc' xcp'"
  and \<tau>move2_WhileCondD: "\<lbrakk> \<tau>move2 P h stk (while (c) b) pc xcp; pc < length (compE2 c) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk c pc xcp"
  and \<tau>move2_ThrowD: "\<lbrakk> \<tau>move2 P h stk (throw e) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e pc xcp"
  and \<tau>move2_Try1D: "\<lbrakk> \<tau>move2 P h stk (try e1 catch(C' V) e2) pc xcp; pc < length (compE2 e1) \<rbrakk> \<Longrightarrow> \<tau>move2 P h stk e1 pc xcp"
apply(auto elim!: \<tau>move2_cases intro: \<tau>move2xcp dest: \<tau>move2_pc_length_compE2)
done

lemma \<tau>move2_Invoke:
  "\<lbrakk>\<tau>move2 P h stk e pc None; compE2 e ! pc = Invoke M n \<rbrakk>
  \<Longrightarrow> n < length stk \<and> (stk ! n = Null \<or> (\<forall>T Ts Tr D. typeof_addr h (the_Addr (stk ! n)) = \<lfloor>T\<rfloor> \<longrightarrow> P \<turnstile> class_type_of T sees M:Ts\<rightarrow>Tr = Native in D \<longrightarrow> \<tau>external_defs D M))"

  and \<tau>moves2_Invoke: 
  "\<lbrakk>\<tau>moves2 P h stk es pc None; compEs2 es ! pc = Invoke M n \<rbrakk> 
  \<Longrightarrow> n < length stk \<and> (stk ! n = Null \<or> (\<forall>T C Ts Tr D. typeof_addr h (the_Addr (stk ! n)) = \<lfloor>T\<rfloor> \<longrightarrow> P \<turnstile> class_type_of T sees M:Ts\<rightarrow>Tr = Native in D \<longrightarrow> \<tau>external_defs D M))"
by(simp_all add: \<tau>move2_iff \<tau>moves2_iff split_beta)

lemmas \<tau>move2_compE2_not_Invoke = \<tau>move2_Invoke
lemmas \<tau>moves2_compEs2_not_Invoke = \<tau>moves2_Invoke

lemma \<tau>move2_blocks1 [simp]:
  "\<tau>move2 P h stk (blocks1 n Ts body) pc' xcp' = \<tau>move2 P h stk body pc' xcp'"
by(simp add: \<tau>move2_iff)

lemma \<tau>instr_stk_append:
  "\<tau>instr P h stk i \<Longrightarrow> \<tau>instr P h (stk @ vs) i"
by(cases i)(auto simp add: nth_append)

lemma \<tau>move2_stk_append:
  "\<tau>move2 P h stk e pc xcp \<Longrightarrow> \<tau>move2 P h (stk @ vs) e pc xcp"
by(simp add: \<tau>move2_iff \<tau>instr_stk_append)

lemma \<tau>moves2_stk_append:
  "\<tau>moves2 P h stk es pc xcp \<Longrightarrow> \<tau>moves2 P h (stk @ vs) es pc xcp"
by(simp add: \<tau>moves2_iff \<tau>instr_stk_append)

fun \<tau>Move2 :: "'addr jvm_prog \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> bool"
where 
  "\<tau>Move2 P (xcp, h, []) = False"
| "\<tau>Move2 P (xcp, h, (stk, loc, C, M, pc) # frs) =
       (let (_,_,_,meth) = method P C M; (_,_,ins,xt) = the meth
        in (pc < length ins \<and> (xcp = None \<longrightarrow> \<tau>instr P h stk (ins ! pc))))"

lemma \<tau>Move2_iff:
  "\<tau>Move2 P \<sigma> = (let (xcp, h, frs) = \<sigma>
                 in case frs of [] \<Rightarrow> False
     | (stk, loc, C, M, pc) # frs' \<Rightarrow> 
       (let (_,_,_,meth) = method P C M; (_,_,ins,xt) = the meth
        in (pc < length ins \<and> (xcp = None \<longrightarrow> \<tau>instr P h stk (ins ! pc)))))"
by(cases \<sigma>)(clarsimp split: list.splits simp add: fun_eq_iff split_beta)

lemma \<tau>instr_compP [simp]: "\<tau>instr (compP f P) h stk i \<longleftrightarrow> \<tau>instr P h stk i"
by(cases i) auto

lemma [simp]: fixes e :: "'addr expr1" and es :: "'addr expr1 list"
  shows \<tau>move2_compP: "\<tau>move2 (compP f P) h stk e = \<tau>move2 P h stk e"
  and \<tau>moves2_compP: "\<tau>moves2 (compP f P) h stk es = \<tau>moves2 P h stk es"
by(auto simp add: \<tau>move2_iff \<tau>moves2_iff fun_eq_iff)

lemma \<tau>Move2_compP2:
  "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>body\<rfloor> in D \<Longrightarrow> 
   \<tau>Move2 (compP2 P) (xcp, h, (stk, loc, C, M, pc) # frs) =
   (case xcp of None \<Rightarrow> \<tau>move2 P h stk body pc xcp \<or> pc = length (compE2 body) | Some a \<Rightarrow> pc < Suc (length (compE2 body)))"
by(clarsimp simp add: \<tau>move2_iff compP2_def compMb2_def nth_append nth_Cons' split: option.splits if_split_asm)

abbreviation \<tau>MOVE2 ::
  "'addr jvm_prog \<Rightarrow> (('addr option \<times> 'addr frame list) \<times> 'heap, ('addr, 'thread_id, 'heap) jvm_thread_action) trsys"
where "\<tau>MOVE2 P \<equiv> \<lambda>((xcp, frs), h) ta s. \<tau>Move2 P (xcp, h, frs) \<and> ta = \<epsilon>"

lemma \<tau>jvmd_heap_unchanged: 
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -\<epsilon>-jvmd\<rightarrow> Normal (xcp', h', frs'); \<tau>Move2 P (xcp, h, frs) \<rbrakk>
  \<Longrightarrow> h = h'"
apply(erule jvmd_NormalE)
apply(clarsimp)
apply(cases xcp)
 apply(rename_tac stk loc C M pc FRS M' Ts T meth mxs mxl ins xt)
 apply(case_tac "ins ! pc")
 prefer 19 \<comment> \<open>BinOpInstr\<close>
 apply(rename_tac bop)
 apply(case_tac "the (binop bop (hd (tl stk)) (hd stk))")
 apply(auto simp add: split_beta \<tau>external_def split: if_split_asm)
apply(fastforce simp add: check_def has_method_def \<tau>external_def dest: \<tau>external_red_external_aggr_heap_unchanged)
done

lemma mexecd_\<tau>mthr_wf:
  "\<tau>multithreaded_wf JVM_final (mexecd P) (\<tau>MOVE2 P)"
proof
  fix t x h ta x' h'
  assume "mexecd P t (x, h) ta (x', h')"
    and "\<tau>MOVE2 P (x, h) ta (x', h')"
  thus "h = h'"
    by(cases x)(cases x', auto dest: \<tau>jvmd_heap_unchanged)
next
  fix s ta s'
  assume "\<tau>MOVE2 P s ta s'" thus "ta = \<epsilon>" by(simp add: split_beta)
qed

end

sublocale JVM_heap_base < execd_mthr: 
  \<tau>multithreaded_wf 
    JVM_final
    "mexecd P"
    convert_RA
    "\<tau>MOVE2 P"
  for P
by(rule mexecd_\<tau>mthr_wf)

context JVM_heap_base begin

lemma \<tau>exec_1_taD:
  assumes exec: "exec_1_d P t (Normal (xcp, h, frs)) ta (Normal (xcp', h', frs'))"
  and \<tau>: "\<tau>Move2 P (xcp, h, frs)"
  shows "ta = \<epsilon>"
using assms
apply(auto elim!: jvmd_NormalE simp add: split_beta)
apply(cases xcp)
apply auto
apply(rename_tac stk loc C M pc FRS)
apply(case_tac "instrs_of P C M ! pc")
apply(simp_all split: if_split_asm)
apply(auto simp add: check_def has_method_def \<tau>external_def dest!: \<tau>external_red_external_aggr_TA_empty)
done

end

end
