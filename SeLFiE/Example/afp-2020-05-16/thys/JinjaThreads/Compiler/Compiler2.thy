(*  Title:      JinjaThreads/Compiler/Compiler2.thy
    Author:     Andreas Lochbihler, Tobias Nipkow
*)

section \<open>Compilation Stage 2\<close>

theory Compiler2
imports PCompiler J1State "../JVM/JVMInstructions"
begin

primrec compE2  :: "'addr expr1      \<Rightarrow> 'addr instr list"
  and compEs2 :: "'addr expr1 list \<Rightarrow> 'addr instr list"
where
  "compE2 (new C) = [New C]"
| "compE2 (newA T\<lfloor>e\<rceil>) = compE2 e @ [NewArray T]"
| "compE2 (Cast T e) = compE2 e @ [Checkcast T]"
| "compE2 (e instanceof T) = compE2 e @ [Instanceof T]"
| "compE2 (Val v) = [Push v]"
| "compE2 (e1 \<guillemotleft>bop\<guillemotright> e2) = compE2 e1 @ compE2 e2 @ [BinOpInstr bop]"
| "compE2 (Var i) = [Load i]"
| "compE2 (i:=e) = compE2 e @ [Store i, Push Unit]"
| "compE2 (a\<lfloor>i\<rceil>) = compE2 a @ compE2 i @ [ALoad]"
| "compE2 (a\<lfloor>i\<rceil> := e) =  compE2 a @ compE2 i @ compE2 e @ [AStore, Push Unit]"
| "compE2 (a\<bullet>length) = compE2 a @ [ALength]"
| "compE2 (e\<bullet>F{D}) = compE2 e @ [Getfield F D]"
| "compE2 (e1\<bullet>F{D} := e2) = compE2 e1 @ compE2 e2 @ [Putfield F D, Push Unit]"
| "compE2 (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) = compE2 e @ compE2 e' @ compE2 e'' @ [CAS F D]"
| "compE2 (e\<bullet>M(es)) = compE2 e @ compEs2 es @ [Invoke M (size es)]"
| "compE2 ({i:T=vo; e}) = (case vo of None \<Rightarrow> [] | \<lfloor>v\<rfloor> \<Rightarrow> [Push v, Store i]) @ compE2 e"
| "compE2 (sync\<^bsub>V\<^esub> (o') e) = compE2 o' @ [Dup, Store V, MEnter] @
                           compE2 e @ [Load V, MExit, Goto 4, Load V, MExit, ThrowExc]"
| "compE2 (insync\<^bsub>V\<^esub> (a) e) = [Goto 1]" \<comment> \<open>Define insync sensibly\<close>
| "compE2 (e1;;e2) = compE2 e1 @ [Pop] @ compE2 e2"
| "compE2 (if (e) e\<^sub>1 else e\<^sub>2) =
          (let cnd   = compE2 e;
               thn   = compE2 e\<^sub>1;
               els   = compE2 e\<^sub>2;
               test  = IfFalse (int(size thn + 2)); 
               thnex = Goto (int(size els + 1))
           in cnd @ [test] @ thn @ [thnex] @ els)"
| "compE2 (while (e) c) =
          (let cnd   = compE2 e;
               bdy   = compE2 c;
               test  = IfFalse (int(size bdy + 3)); 
               loop  = Goto (-int(size bdy + size cnd + 2))
           in cnd @ [test] @ bdy @ [Pop] @ [loop] @ [Push Unit])"
| "compE2 (throw e) = compE2 e @ [ThrowExc]"
| "compE2 (try e1 catch(C i) e2) =
   (let catch = compE2 e2
    in compE2 e1 @ [Goto (int(size catch)+2), Store i] @ catch)"

| "compEs2 []     = []"
| "compEs2 (e#es) = compE2 e @ compEs2 es"


text\<open>Compilation of exception table. Is given start address of code
to compute absolute addresses necessary in exception table.\<close>


fun compxE2  :: "'addr expr1      \<Rightarrow> pc \<Rightarrow> nat \<Rightarrow> ex_table"
and compxEs2 :: "'addr expr1 list \<Rightarrow> pc \<Rightarrow> nat \<Rightarrow> ex_table"
where
  "compxE2 (new C) pc d = []"
| "compxE2 (newA T\<lfloor>e\<rceil>) pc d = compxE2 e pc d"
| "compxE2 (Cast T e) pc d = compxE2 e pc d"
| "compxE2 (e instanceof T) pc d = compxE2 e pc d"
| "compxE2 (Val v) pc d = []"
| "compxE2 (e1 \<guillemotleft>bop\<guillemotright> e2) pc d =
   compxE2 e1 pc d @ compxE2 e2 (pc + size(compE2 e1)) (d+1)"
| "compxE2 (Var i) pc d = []"
| "compxE2 (i:=e) pc d = compxE2 e pc d"
| "compxE2 (a\<lfloor>i\<rceil>) pc d = compxE2 a pc d @ compxE2 i (pc + size (compE2 a)) (d + 1)"
| "compxE2 (a\<lfloor>i\<rceil> := e) pc d =
         (let pc1 = pc  + size (compE2 a);
              pc2 = pc1 + size (compE2 i)
          in compxE2 a pc d @ compxE2 i pc1 (d + 1) @ compxE2 e pc2 (d + 2))"
| "compxE2 (a\<bullet>length) pc d = compxE2 a pc d"
| "compxE2 (e\<bullet>F{D}) pc d = compxE2 e pc d"
| "compxE2 (e1\<bullet>F{D} := e2) pc d = compxE2 e1 pc d @ compxE2 e2 (pc + size (compE2 e1)) (d + 1)"
| "compxE2 (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) pc d = 
   (let pc1 = pc  + size (compE2 e);
        pc2 = pc1 + size (compE2 e')
    in compxE2 e pc d @ compxE2 e' pc1 (d + 1) @ compxE2 e'' pc2 (d + 2))"
| "compxE2 (e\<bullet>M(es)) pc d = compxE2 e pc d @ compxEs2 es (pc + size(compE2 e)) (d+1)"
| "compxE2 ({i:T=vo; e}) pc d = compxE2 e (case vo of None \<Rightarrow> pc | \<lfloor>v\<rfloor> \<Rightarrow> Suc (Suc pc)) d"
| "compxE2 (sync\<^bsub>V\<^esub> (o') e) pc d =
           (let pc1 = pc + size (compE2 o') + 3;
                pc2 = pc1 + size(compE2 e)
            in compxE2 o' pc d @ compxE2 e pc1 d @ [(pc1, pc2, None, Suc (Suc (Suc pc2)), d)])"
| "compxE2 (insync\<^bsub>V\<^esub> (a) e) pc d = []"
| "compxE2 (e1;;e2) pc d =
   compxE2 e1 pc d @ compxE2 e2 (pc+size(compE2 e1)+1) d"
| "compxE2 (if (e) e\<^sub>1 else e\<^sub>2) pc d =
           (let pc\<^sub>1   = pc + size(compE2 e) + 1;
                pc\<^sub>2   = pc\<^sub>1 + size(compE2 e\<^sub>1) + 1
            in compxE2 e pc d @ compxE2 e\<^sub>1 pc\<^sub>1 d @ compxE2 e\<^sub>2 pc\<^sub>2 d)"
| "compxE2 (while (b) e) pc d =
   compxE2 b pc d @ compxE2 e (pc+size(compE2 b)+1) d"
| "compxE2 (throw e) pc d = compxE2 e pc d"
| "compxE2 (try e1 catch(C i) e2) pc d =
   (let pc1 = pc + size(compE2 e1)
    in compxE2 e1 pc d @ compxE2 e2 (pc1+2) d @ [(pc,pc1,Some C,pc1+1,d)])"

| "compxEs2 [] pc d    = []"
| "compxEs2 (e#es) pc d = compxE2 e pc d @ compxEs2 es (pc+size(compE2 e)) (d+1)"

lemmas compxE2_compxEs2_induct =
  compxE2_compxEs2.induct[
    unfolded meta_all5_eq_conv meta_all4_eq_conv meta_all3_eq_conv meta_all2_eq_conv meta_all_eq_conv,
    case_names
      new NewArray Cast InstanceOf Val BinOp Var LAss AAcc AAss ALen FAcc FAss Call Block
      Synchronized InSynchronized Seq Cond While throw TryCatch
      Nil Cons]

lemma compE2_neq_Nil [simp]: "compE2 e \<noteq> []"
by(induct e) auto

declare compE2_neq_Nil[symmetric, simp]

lemma compEs2_append [simp]: "compEs2 (es @ es') = compEs2 es @ compEs2 es'"
by(induct es) auto

lemma compEs2_eq_Nil_conv [simp]: "compEs2 es = [] \<longleftrightarrow> es = []"
by(cases es) auto

lemma compEs2_map_Val: "compEs2 (map Val vs) = map Push vs"
by(induct vs) auto

lemma compE2_0th_neq_Invoke [simp]:
  "compE2 e ! 0 \<noteq> Invoke M n"
by(induct e)(auto simp add: nth_append)

declare compE2_0th_neq_Invoke[symmetric, simp]

lemma compxEs2_append [simp]:
  "compxEs2 (es @ es') pc d = compxEs2 es pc d @ compxEs2 es' (length (compEs2 es) + pc) (length es + d)"
by(induct es arbitrary: pc d)(auto simp add: ac_simps)

lemma compxEs2_map_Val [simp]: "compxEs2 (map Val vs) pc d = []"
by(induct vs arbitrary: d pc) auto

lemma compE2_blocks1 [simp]:
  "compE2 (blocks1 n Ts body) = compE2 body"
by(induct n Ts body rule: blocks1.induct)(auto)

lemma compxE2_blocks1 [simp]:
  "compxE2 (blocks1 n Ts body) = compxE2 body"
by(induct n Ts body rule: blocks1.induct)(auto intro!: ext)

lemma fixes e :: "'addr expr1" and es :: "'addr expr1 list"
  shows compE2_not_Return: "Return \<notin> set (compE2 e)"
  and compEs2_not_Return: "Return \<notin> set (compEs2 es)"
by(induct e and es rule: compE2.induct compEs2.induct)(auto)

primrec max_stack :: "'addr expr1 \<Rightarrow> nat"
  and max_stacks :: "'addr expr1 list \<Rightarrow> nat"
where
  "max_stack (new C) = 1"
| "max_stack (newA T\<lfloor>e\<rceil>) = max_stack e"
| "max_stack (Cast C e) = max_stack e"
| "max_stack (e instanceof T) = max_stack e"
| "max_stack (Val v) = 1"
| "max_stack (e1 \<guillemotleft>bop\<guillemotright> e2) = max (max_stack e1) (max_stack e2) + 1"
| "max_stack (Var i) = 1"
| "max_stack (i:=e) = max_stack e"
| "max_stack (a\<lfloor>i\<rceil>) = max (max_stack a) (max_stack i + 1)"
| "max_stack (a\<lfloor>i\<rceil> := e) = max (max (max_stack a) (max_stack i + 1)) (max_stack e + 2)"
| "max_stack (a\<bullet>length) = max_stack a"
| "max_stack (e\<bullet>F{D}) = max_stack e"
| "max_stack (e1\<bullet>F{D} := e2) = max (max_stack e1) (max_stack e2) + 1"
| "max_stack (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) = max (max (max_stack e) (max_stack e' + 1)) (max_stack e'' + 2)"
| "max_stack (e\<bullet>M(es)) = max (max_stack e) (max_stacks es) + 1"
| "max_stack ({i:T=vo; e}) = max_stack e"
| "max_stack (sync\<^bsub>V\<^esub> (o') e) = max (max_stack o') (max (max_stack e) 2)"
| "max_stack (insync\<^bsub>V\<^esub> (a) e) = 1"
| "max_stack (e1;;e2) = max (max_stack e1) (max_stack e2)"
| "max_stack (if (e) e\<^sub>1 else e\<^sub>2) =
   max (max_stack e) (max (max_stack e\<^sub>1) (max_stack e\<^sub>2))"
| "max_stack (while (e) c) = max (max_stack e) (max_stack c)"
| "max_stack (throw e) = max_stack e"
| "max_stack (try e1 catch(C i) e2) = max (max_stack e1) (max_stack e2)"

| "max_stacks [] = 0"
| "max_stacks (e#es) = max (max_stack e) (1 + max_stacks es)"

lemma max_stack1: "1 \<le> max_stack e"
(*<*)by(induct e) (simp_all add:max_def)(*>*)

lemma max_stacks_ge_length: "max_stacks es \<ge> length es"
by(induct es, auto)

lemma max_stack_blocks1 [simp]:
  "max_stack (blocks1 n Ts body) = max_stack body"
by(induct n Ts body rule: blocks1.induct) auto

definition compMb2 :: "'addr expr1 \<Rightarrow> 'addr jvm_method"
where
  "compMb2  \<equiv>  \<lambda>body.
  let ins = compE2 body @ [Return];
      xt = compxE2 body 0 0
  in (max_stack body, max_vars body, ins, xt)"

definition compP2 :: "'addr J1_prog \<Rightarrow> 'addr jvm_prog"
where "compP2  \<equiv>  compP (\<lambda>C M Ts T. compMb2)"

lemma compMb2:
  "compMb2 e = (max_stack e, max_vars e, (compE2 e @ [Return]), compxE2 e 0 0)"
by (simp add: compMb2_def)

end
