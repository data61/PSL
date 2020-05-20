(*  Title:      JinjaThreads/Compiler/Execs.thy
    Author:     Andreas Lochbihler
*)

section \<open>JVM Semantics for the delay bisimulation proof from intermediate language to byte code\<close>

theory Execs imports JVMTau begin

declare match_ex_table_app [simp del]
  match_ex_table_eq_NoneI [simp del]
  compxE2_size_convs [simp del]
  compxE2_stack_xlift_convs [simp del]
  compxEs2_stack_xlift_convs [simp del]

type_synonym
  ('addr, 'heap) check_instr' = 
  "'addr instr \<Rightarrow> 'addr jvm_prog \<Rightarrow> 'heap \<Rightarrow> 'addr val list \<Rightarrow> 'addr val list \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> pc \<Rightarrow> 'addr frame list \<Rightarrow> bool"

primrec check_instr' :: "('addr, 'heap) check_instr'"
where 
check_instr'_Load:
  "check_instr' (Load n) P h stk loc C M\<^sub>0 pc frs =
  True"

| check_instr'_Store:
  "check_instr' (Store n) P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (0 < length stk)"

| check_instr'_Push:
  "check_instr' (Push v) P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  True"

| check_instr'_New:
  "check_instr' (New C) P h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
  True"

| check_instr'_NewArray:
  "check_instr' (NewArray T) P h stk loc C0 M0 pc frs =
  (0 < length stk)"

| check_instr'_ALoad:
  "check_instr' ALoad P h stk loc C0 M0 pc frs =
  (1 < length stk)"

| check_instr'_AStore:
  "check_instr' AStore P h stk loc C0 M0 pc frs =
  (2 < length stk)"

| check_instr'_ALength:
  "check_instr' ALength P h stk loc C0 M0 pc frs =
  (0 < length stk)"

| check_instr'_Getfield:
  "check_instr' (Getfield F C) P h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
  (0 < length stk)"

| check_instr'_Putfield:
  "check_instr' (Putfield F C) P h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
  (1 < length stk)"

| check_instr'_CAS:
  "check_instr' (CAS F C) P h stk loc C\<^sub>0 M\<^sub>0 pc frs  =
  (2 < length stk)"

| check_instr'_Checkcast:
  "check_instr' (Checkcast T) P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (0 < length stk)"

| check_instr'_Instanceof:
  "check_instr' (Instanceof T) P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (0 < length stk)"

| check_instr'_Invoke:
  "check_instr' (Invoke M n) P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (n < length stk)"

| check_instr'_Return:
  "check_instr' Return P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (0 < length stk)"
 
| check_instr'_Pop:
  "check_instr' Pop P h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
  (0 < length stk)"

| check_instr'_Dup:
  "check_instr' Dup P h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
  (0 < length stk)"

| check_instr'_Swap:
  "check_instr' Swap P h stk loc C\<^sub>0 M\<^sub>0 pc frs = 
  (1 < length stk)"

| check_instr'_BinOpInstr:
  "check_instr' (BinOpInstr bop) P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (1 < length stk)"

| check_instr'_IfFalse:
  "check_instr' (IfFalse b) P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (0 < length stk \<and> 0 \<le> int pc+b)"

| check_instr'_Goto:
  "check_instr' (Goto b) P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (0 \<le> int pc+b)"

| check_instr'_Throw:
  "check_instr' ThrowExc P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
  (0 < length stk)"

| check_instr'_MEnter:
  "check_instr' MEnter P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
   (0 < length stk)"

| check_instr'_MExit:
  "check_instr' MExit P h stk loc C\<^sub>0 M\<^sub>0 pc frs =
   (0 < length stk)"

definition ci_stk_offer :: "('addr, 'heap) check_instr' \<Rightarrow> bool"
where
  "ci_stk_offer ci =
  (\<forall>ins P h stk stk' loc C M pc frs. ci ins P h stk loc C M pc frs \<longrightarrow> ci ins P h (stk @ stk') loc C M pc frs)"

lemma ci_stk_offerI:
  "(\<And>ins P h stk stk' loc C M pc frs. ci ins P h stk loc C M pc frs \<Longrightarrow> ci ins P h (stk @ stk') loc C M pc frs) \<Longrightarrow> ci_stk_offer ci"
unfolding ci_stk_offer_def by blast

lemma ci_stk_offerD:
  "\<lbrakk> ci_stk_offer ci; ci ins P h stk loc C M pc frs \<rbrakk> \<Longrightarrow> ci ins P h (stk @ stk') loc C M pc frs"
unfolding ci_stk_offer_def by blast


lemma check_instr'_stk_offer:
  "ci_stk_offer check_instr'"
proof(rule ci_stk_offerI)
  fix ins P h stk stk' loc C M pc frs
  assume "check_instr' ins P h stk loc C M pc frs"
  thus "check_instr' ins P h (stk @ stk') loc C M pc frs"
    by(cases ins) auto
qed

context JVM_heap_base begin

lemma check_instr_imp_check_instr':
  "check_instr ins P h stk loc C M pc frs \<Longrightarrow> check_instr' ins P h stk loc C M pc frs"
by(cases ins) auto

lemma check_instr_stk_offer:
  "ci_stk_offer check_instr"
proof(rule ci_stk_offerI)
  fix ins P h stk stk' loc C M pc frs
  assume "check_instr ins P h stk loc C M pc frs"
  thus "check_instr ins P h (stk @ stk') loc C M pc frs"
    by(cases ins)(auto simp add: nth_append hd_append neq_Nil_conv tl_append split: list.split)
qed

end

(* TODO: Combine ins_jump_ok and jump_ok *)
primrec jump_ok :: "'addr instr list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where "jump_ok [] n n' = True"
| "jump_ok (x # xs) n n' = (jump_ok xs (Suc n) n' \<and> 
                           (case x of IfFalse m \<Rightarrow> - int n \<le> m \<and> m \<le> int (n' + length xs)
                                       | Goto m \<Rightarrow> - int n \<le> m \<and> m \<le> int (n' + length xs)
                                            | _ \<Rightarrow> True))"

lemma jump_ok_append [simp]:
  "jump_ok (xs @ xs') n n' \<longleftrightarrow> jump_ok xs n (n' + length xs') \<and> jump_ok xs' (n + length xs) n'"
apply(induct xs arbitrary: n)
 apply(simp)
apply(auto split: instr.split)
done

lemma jump_ok_GotoD:
  "\<lbrakk> jump_ok ins n n'; ins ! pc = Goto m; pc < length ins \<rbrakk> \<Longrightarrow> - int (pc + n) \<le> m \<and> m < int (length ins - pc + n')"
apply(induct ins arbitrary: n n' pc)
 apply(simp)
apply(clarsimp)
apply(case_tac pc)
apply(fastforce)+
done

lemma jump_ok_IfFalseD:
  "\<lbrakk> jump_ok ins n n'; ins ! pc = IfFalse m; pc < length ins \<rbrakk> \<Longrightarrow> - int (pc + n) \<le> m \<and> m < int (length ins - pc + n')"
apply(induct ins arbitrary: n n' pc)
 apply(simp)
apply(clarsimp)
apply(case_tac pc)
apply(fastforce)+
done

lemma fixes e :: "'addr expr1" and es :: "'addr expr1 list"
  shows compE2_jump_ok [intro!]: "jump_ok (compE2 e) n (Suc n')"
  and compEs2_jump_ok [intro!]: "jump_ok (compEs2 es) n (Suc n')"
apply(induct e and es arbitrary: n n' and n n' rule: compE2.induct compEs2.induct)
apply(auto split: bop.split)
done

lemma fixes e :: "'addr expr1" and es :: "'addr expr1 list"
  shows compE1_Goto_not_same: "\<lbrakk> compE2 e ! pc = Goto i; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> nat (int pc + i) \<noteq> pc"
  and compEs2_Goto_not_same: "\<lbrakk> compEs2 es ! pc = Goto i; pc < length (compEs2 es) \<rbrakk> \<Longrightarrow> nat (int pc + i) \<noteq> pc"
apply(induct e and es arbitrary: pc i and pc i rule: compE2.induct compEs2.induct)
apply(auto simp add: nth_Cons nth_append split: if_split_asm bop.split_asm nat.splits)
apply fastforce+
done

fun ins_jump_ok :: "'addr instr \<Rightarrow> nat \<Rightarrow> bool"
where
  "ins_jump_ok (Goto m) l = (- (int l) \<le> m)"
| "ins_jump_ok (IfFalse m) l = (- (int l) \<le> m)"
| "ins_jump_ok _ _ = True"

definition wf_ci :: "('addr, 'heap) check_instr' \<Rightarrow> bool"
where
  "wf_ci ci \<longleftrightarrow>
   ci_stk_offer ci \<and> ci \<le> check_instr' \<and>
   (\<forall>ins P h stk loc C M pc pc' frs. ci ins P h stk loc C M pc frs \<longrightarrow> ins_jump_ok ins pc' \<longrightarrow> ci ins P h stk loc C M pc' frs)"

lemma wf_ciI:
  "\<lbrakk> ci_stk_offer ci;
    \<And>ins P h stk loc C M pc frs. ci ins P h stk loc C M pc frs \<Longrightarrow> check_instr' ins P h stk loc C M pc frs;
    \<And>ins P h stk loc C M pc pc' frs. \<lbrakk> ci ins P h stk loc C M pc frs; ins_jump_ok ins pc' \<rbrakk> \<Longrightarrow> ci ins P h stk loc C M pc' frs \<rbrakk>
  \<Longrightarrow> wf_ci ci"
unfolding wf_ci_def le_fun_def le_bool_def
by blast

lemma check_instr'_pc:
  "\<lbrakk> check_instr' ins P h stk loc C M pc frs; ins_jump_ok ins pc' \<rbrakk> \<Longrightarrow> check_instr' ins P h stk loc C M pc' frs"
by(cases ins) auto

lemma wf_ci_check_instr' [iff]:
  "wf_ci check_instr'"
apply(rule wf_ciI)
  apply(rule check_instr'_stk_offer)
 apply(assumption)
apply(erule (1) check_instr'_pc)
done

lemma jump_ok_ins_jump_ok:
  "\<lbrakk> jump_ok ins n n'; pc < length ins \<rbrakk> \<Longrightarrow> ins_jump_ok (ins ! pc) (pc + n)"
apply(induct ins arbitrary: n n' pc)
apply(fastforce simp add: nth_Cons' gr0_conv_Suc split: instr.split_asm)+
done

context JVM_heap_base begin

lemma check_instr_pc:
  "\<lbrakk> check_instr ins P h stk loc C M pc frs; ins_jump_ok ins pc' \<rbrakk> \<Longrightarrow> check_instr ins P h stk loc C M pc' frs"
by(cases ins) auto

lemma wf_ci_check_instr [iff]:
  "wf_ci check_instr"
apply(rule wf_ciI)
  apply(rule check_instr_stk_offer)
 apply(erule check_instr_imp_check_instr')
apply(erule (1) check_instr_pc)
done

end

lemma wf_ciD1: "wf_ci ci \<Longrightarrow> ci_stk_offer ci"
unfolding wf_ci_def by blast

lemma wf_ciD2: "\<lbrakk> wf_ci ci; ci ins P h stk loc C M pc frs \<rbrakk> \<Longrightarrow> check_instr' ins P h stk loc C M pc frs"
unfolding wf_ci_def le_fun_def le_bool_def
by blast

lemma wf_ciD3: "\<lbrakk> wf_ci ci; ci ins P h stk loc C M pc frs; ins_jump_ok ins pc' \<rbrakk> \<Longrightarrow> ci ins P h stk loc C M pc' frs"
unfolding wf_ci_def by blast

lemma check_instr'_ins_jump_ok: "check_instr' ins P h stk loc C M pc frs \<Longrightarrow> ins_jump_ok ins pc"
by(cases ins) auto
lemma wf_ci_ins_jump_ok:
  assumes wf: "wf_ci ci"
  and ci: "ci ins P h stk loc C M pc frs"
  and pc': "pc \<le> pc'"
  shows "ins_jump_ok ins pc'"
proof -
  from wf ci have "check_instr' ins P h stk loc C M pc frs" by(rule wf_ciD2)
  with pc' have "check_instr' ins P h stk loc C M pc' frs" by(cases ins) auto
  thus ?thesis by(rule check_instr'_ins_jump_ok)
qed

lemma wf_ciD3': "\<lbrakk> wf_ci ci; ci ins P h stk loc C M pc frs; pc \<le> pc' \<rbrakk> \<Longrightarrow> ci ins P h stk loc C M pc' frs"
apply(frule (2) wf_ci_ins_jump_ok)
apply(erule (2) wf_ciD3)
done

typedef ('addr, 'heap) check_instr = "Collect wf_ci :: ('addr, 'heap) check_instr' set"
  morphisms ci_app Abs_check_instr
by auto

lemma ci_app_check_instr' [simp]: "ci_app (Abs_check_instr check_instr') = check_instr'"
by(simp add: Abs_check_instr_inverse)

lemma (in JVM_heap_base) ci_app_check_instr [simp]: "ci_app (Abs_check_instr check_instr) = check_instr"
by(simp add: Abs_check_instr_inverse)

lemma wf_ci_stk_offerD:
  "ci_app ci ins P h stk loc C M pc frs \<Longrightarrow> ci_app ci ins P h (stk @ stk') loc C M pc frs"
apply(rule ci_stk_offerD[OF wf_ciD1]) back
by(rule ci_app [simplified])

lemma wf_ciD2_ci_app:
  "ci_app ci ins P h stk loc C M pc frs \<Longrightarrow> check_instr' ins P h stk loc C M pc frs"
apply(cases ci)
apply(simp add: Abs_check_instr_inverse)
apply(erule (1) wf_ciD2)
done

lemma wf_ciD3_ci_app:
  "\<lbrakk> ci_app ci ins P h stk loc C M pc frs; ins_jump_ok ins pc' \<rbrakk> \<Longrightarrow> ci_app ci ins P h stk loc C M pc' frs"
apply(cases ci)
apply(simp add: Abs_check_instr_inverse)
apply(erule (2) wf_ciD3)
done

lemma wf_ciD3'_ci_app: "\<lbrakk> ci_app ci ins P h stk loc C M pc frs; pc \<le> pc' \<rbrakk> \<Longrightarrow> ci_app ci ins P h stk loc C M pc' frs"
apply(cases ci)
apply(simp add: Abs_check_instr_inverse)
apply(erule (2) wf_ciD3')
done

context JVM_heap_base begin

inductive exec_meth ::
  "('addr, 'heap) check_instr \<Rightarrow> 'addr jvm_prog \<Rightarrow> 'addr instr list \<Rightarrow> ex_table \<Rightarrow> 'thread_id
  \<Rightarrow> 'heap \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action
  \<Rightarrow> 'heap \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"
for ci :: "('addr, 'heap) check_instr" and P :: "'addr jvm_prog" 
and ins :: "'addr instr list" and xt :: "ex_table" and t :: 'thread_id
where
  exec_instr: 
  "\<lbrakk> (ta, xcp, h', [(stk', loc', undefined, undefined, pc')]) \<in> exec_instr (ins ! pc) P t h stk loc undefined undefined pc [];
     pc < length ins;
     ci_app ci (ins ! pc) P h stk loc undefined undefined pc [] \<rbrakk>
  \<Longrightarrow> exec_meth ci P ins xt t h (stk, loc, pc, None) ta h' (stk', loc', pc', xcp)"

| exec_catch:
  "\<lbrakk> match_ex_table P (cname_of h xcp) pc xt = \<lfloor>(pc', d)\<rfloor>; d \<le> length stk \<rbrakk>
  \<Longrightarrow> exec_meth ci P ins xt t h (stk, loc, pc, \<lfloor>xcp\<rfloor>) \<epsilon> h (Addr xcp # drop (size stk - d) stk, loc, pc', None)"

lemma exec_meth_instr:
  "exec_meth ci P ins xt t h (stk, loc, pc, None) ta h' (stk', loc', pc', xcp) \<longleftrightarrow>
   (ta, xcp, h', [(stk', loc', undefined, undefined, pc')]) \<in> exec_instr (ins ! pc) P t h stk loc undefined undefined pc [] \<and> pc < length ins \<and> ci_app ci (ins ! pc) P h stk loc undefined undefined pc []"
by(auto elim: exec_meth.cases intro: exec_instr)

lemma exec_meth_xcpt:
  "exec_meth ci P ins xt t h (stk, loc, pc, \<lfloor>xcp\<rfloor>) ta h (stk', loc', pc', xcp') \<longleftrightarrow>
   (\<exists>d. match_ex_table P (cname_of h xcp) pc xt = \<lfloor>(pc', d)\<rfloor> \<and> ta = \<epsilon> \<and> stk' = (Addr xcp # drop (size stk - d) stk) \<and> loc' = loc \<and> xcp' = None \<and> d \<le> length stk)"
by(auto elim: exec_meth.cases intro: exec_catch)

abbreviation exec_meth_a
where "exec_meth_a \<equiv> exec_meth (Abs_check_instr check_instr')"

abbreviation exec_meth_d
where "exec_meth_d \<equiv> exec_meth (Abs_check_instr check_instr)"

lemma exec_meth_length_compE2D [dest]:
  "exec_meth ci P (compE2 e) (compxE2 e 0 d) t h (stk, loc, pc, xcp) ta h' s' \<Longrightarrow> pc < length (compE2 e)"
apply(erule exec_meth.cases)
apply(auto dest: match_ex_table_pc_length_compE2)
done

lemma exec_meth_length_compEs2D [dest]:
  "exec_meth ci P (compEs2 es) (compxEs2 es 0 0) t h (stk, loc, pc, xcp) ta h' s' \<Longrightarrow> pc < length (compEs2 es)"
apply(erule exec_meth.cases)
apply(auto dest: match_ex_table_pc_length_compEs2)
done

lemma exec_instr_stk_offer:
  assumes check: "check_instr' (ins ! pc) P h stk loc C M pc frs"
  and exec: "(ta', xcp', h', (stk', loc', C, M, pc') # frs) \<in> exec_instr (ins ! pc) P t h stk loc C M pc frs"
  shows "(ta', xcp', h', (stk' @ stk'', loc', C, M, pc') # frs) \<in> exec_instr (ins ! pc) P t h (stk @ stk'') loc C M pc frs"
using assms
proof(cases "ins ! pc")
  case (Invoke M n)
  thus ?thesis using exec check
    by(auto split: if_split_asm extCallRet.splits split del: if_split simp add: split_beta nth_append min_def extRet2JVM_def)
qed(force simp add: nth_append is_Ref_def has_method_def nth_Cons split_beta hd_append tl_append neq_Nil_conv split: list.split if_split_asm nat.splits sum.split_asm)+

lemma exec_meth_stk_offer:
  assumes exec: "exec_meth ci P ins xt t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_meth ci P ins (stack_xlift (length stk'') xt) t h (stk @ stk'', loc, pc, xcp) ta h' (stk' @ stk'', loc', pc', xcp')"
using exec
proof(cases)
  case (exec_catch xcp d)
  from \<open>match_ex_table P (cname_of h xcp) pc xt = \<lfloor>(pc', d)\<rfloor>\<close>
  have "match_ex_table P (cname_of h xcp) pc (stack_xlift (length stk'') xt) = \<lfloor>(pc', length stk'' + d)\<rfloor>"
    by(simp add: match_ex_table_stack_xlift)
  moreover have "length stk'' + d \<le> length (stk @ stk'')" using \<open>d \<le> length stk\<close> by simp
  ultimately have "exec_meth ci P ins (stack_xlift (length stk'') xt) t h ((stk @ stk''), loc, pc, \<lfloor>xcp\<rfloor>) \<epsilon> h ((Addr xcp # drop (length (stk @ stk'') - (length stk'' + d)) (stk @ stk'')), loc, pc', None)"
    by(rule exec_meth.exec_catch)
  with exec_catch show ?thesis by(simp)
next
  case exec_instr
  note ciins = \<open>ci_app ci (ins ! pc) P h stk loc undefined undefined pc []\<close>
  hence "ci_app ci (ins ! pc) P h (stk @ stk'') loc undefined undefined pc []"
    by(rule wf_ci_stk_offerD)
  moreover from ciins
  have "check_instr' (ins ! pc) P h stk loc undefined undefined  pc []"
    by(rule wf_ciD2_ci_app)
  hence "(ta, xcp', h', [(stk' @ stk'', loc', undefined, undefined, pc')]) \<in> exec_instr (ins ! pc) P t h (stk @ stk'') loc undefined undefined pc []"
    using \<open>(ta, xcp', h', [(stk', loc', undefined,undefined , pc')]) \<in> exec_instr (ins ! pc) P t h stk loc undefined undefined pc []\<close>
    by(rule exec_instr_stk_offer)
  ultimately show ?thesis using exec_instr by(auto intro: exec_meth.exec_instr)
qed
  
lemma exec_meth_append_xt [intro]:
  "exec_meth ci P ins xt t h s ta h' s'
  \<Longrightarrow> exec_meth ci P (ins @ ins') (xt @ xt') t h s ta h' s'"
apply(erule exec_meth.cases)
 apply(auto)
 apply(rule exec_instr)
   apply(clarsimp simp add: nth_append)
  apply(simp)
 apply(simp add: nth_append)
apply(rule exec_catch)
by(simp)

lemma exec_meth_append [intro]:
  "exec_meth ci P ins xt t h s ta h' s' \<Longrightarrow> exec_meth ci P (ins @ ins') xt t h s ta h' s'"
by(rule exec_meth_append_xt[where xt'="[]", simplified])

lemma append_exec_meth_xt:
  assumes exec: "exec_meth ci P ins xt t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  and jump: "jump_ok ins 0 n"
  and pcs: "pcs xt' \<subseteq> {0..<length ins'}"
  shows "exec_meth ci P (ins' @ ins) (xt' @ shift (length ins') xt) t h (stk, loc, (length ins' + pc), xcp) ta h' (stk', loc', (length ins' + pc'), xcp')"
using exec
proof(cases)
  case (exec_catch xcp d)
  from \<open>match_ex_table P (cname_of h xcp) pc xt = \<lfloor>(pc', d)\<rfloor>\<close>
  have "match_ex_table P (cname_of h xcp) (length ins' + pc) (shift (length ins') xt) = \<lfloor>(length ins' + pc', d)\<rfloor>"
    by(simp add: match_ex_table_shift)
  moreover from pcs have "length ins' + pc \<notin> pcs xt'" by(auto)
  ultimately have "match_ex_table P (cname_of h xcp) (length ins' + pc) (xt' @ shift (length ins') xt) = \<lfloor>(length ins' + pc', d)\<rfloor>"
    by(simp add: match_ex_table_append_not_pcs)
  with exec_catch show ?thesis by(auto dest: exec_meth.exec_catch)
next
  case exec_instr
  note exec = \<open>(ta, xcp', h', [(stk', loc', undefined, undefined, pc')]) \<in> exec_instr (ins ! pc) P t h stk loc undefined undefined pc []\<close>
  hence "(ta, xcp', h', [(stk', loc', undefined, undefined, length ins' + pc')]) \<in> exec_instr (ins ! pc) P t h stk loc undefined undefined (length ins' + pc) []"
  proof(cases "ins ! pc")
    case (Goto i)
    with jump \<open>pc < length ins\<close> have "- int pc  \<le> i" "i < int (length ins - pc + n)"
      by(auto dest: jump_ok_GotoD)
    with exec Goto show ?thesis by(auto)
  next
    case (IfFalse i)
    with jump \<open>pc < length ins\<close> have "- int pc  \<le> i" "i < int (length ins - pc + n)"
      by(auto dest: jump_ok_IfFalseD)
    with exec IfFalse show ?thesis by(auto)
  next
    case (Invoke M n)
    with exec show ?thesis 
      by(auto split: if_split_asm extCallRet.splits split del: if_split simp add: split_beta nth_append min_def extRet2JVM_def)
  qed(auto simp add: split_beta split: if_split_asm sum.split_asm)
  moreover from \<open>ci_app ci (ins ! pc) P h stk loc undefined undefined pc []\<close>
  have "ci_app ci (ins ! pc) P h stk loc undefined undefined (length ins' + pc) []"
    by(rule wf_ciD3'_ci_app) simp
  ultimately have "exec_meth ci P (ins' @ ins) (xt' @ shift (length ins') xt) t h (stk, loc, (length ins' + pc), None) ta h' (stk', loc', (length ins' + pc'), xcp')"
    using \<open>pc < length ins\<close> by -(rule exec_meth.exec_instr, simp_all)
  thus ?thesis using exec_instr by(auto)
qed

lemma append_exec_meth:
  assumes exec: "exec_meth ci P ins xt t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  and jump: "jump_ok ins 0 n"
  shows "exec_meth ci P (ins' @ ins) (shift (length ins') xt) t h (stk, loc, (length ins' + pc), xcp) ta h' (stk', loc', (length ins' + pc'), xcp')"
using assms by(rule append_exec_meth_xt [where xt'="[]", simplified])

lemma exec_meth_take_xt':
  "\<lbrakk> exec_meth ci P (ins @ ins') (xt' @ xt) t h (stk, loc, pc, xcp) ta h' s';
    pc < length ins; pc \<notin> pcs xt \<rbrakk>
  \<Longrightarrow> exec_meth ci P ins xt' t h (stk, loc, pc, xcp) ta h' s'"
apply(erule exec_meth.cases)
apply(auto intro: exec_meth.intros simp add: match_ex_table_append nth_append dest: match_ex_table_pcsD)
done

lemma exec_meth_take_xt:
  "\<lbrakk> exec_meth ci P (ins @ ins') (xt' @ shift (length ins) xt) t h (stk, loc, pc, xcp) ta h' s';
    pc < length ins \<rbrakk>
  \<Longrightarrow> exec_meth ci P ins xt' t h (stk, loc, pc, xcp) ta h' s'"
by(auto intro: exec_meth_take_xt')

lemma exec_meth_take:
  "\<lbrakk> exec_meth ci P (ins @ ins') xt t h (stk, loc, pc, xcp) ta h' s';
    pc < length ins \<rbrakk>
  \<Longrightarrow> exec_meth ci P ins xt t h (stk, loc, pc, xcp) ta h' s'"
by(auto intro: exec_meth_take_xt[where xt = "[]"])


lemma exec_meth_drop_xt:
  assumes exec: "exec_meth ci P (ins @ ins') (xt @ shift (length ins) xt') t h (stk, loc, (length ins + pc), xcp) ta h' (stk', loc', pc', xcp')"
  and xt: "pcs xt \<subseteq> {..<length ins}"
  and jump: "jump_ok ins' 0 n"
  shows "exec_meth ci P ins' xt' t h (stk, loc, pc, xcp) ta h' (stk', loc', (pc' - length ins), xcp')"
using exec
proof(cases rule: exec_meth.cases)
  case exec_instr
  let ?PC = "length ins + pc"
  note [simp] = \<open>xcp = None\<close>
  from \<open>?PC < length (ins @ ins')\<close> have pc: "pc < length ins'" by simp
  moreover with \<open>(ta, xcp', h', [(stk', loc', undefined, undefined, pc')]) \<in> exec_instr ((ins @ ins') ! ?PC) P t h stk loc undefined undefined ?PC []\<close>
  have "(ta, xcp', h', [(stk', loc', undefined, undefined, pc' - length ins)]) \<in> exec_instr (ins' ! pc) P t h stk loc undefined undefined pc []"
    apply(cases "ins' ! pc")
    apply(simp_all add: split_beta split: if_split_asm sum.split_asm split del: if_split)
    apply(force split: extCallRet.splits simp add: min_def extRet2JVM_def)+
    done
  moreover from \<open>ci_app ci ((ins @ ins') ! ?PC) P h stk loc undefined undefined ?PC []\<close> jump pc
  have "ci_app ci (ins' ! pc) P h stk loc undefined undefined pc []"
    by(fastforce elim: wf_ciD3_ci_app dest: jump_ok_ins_jump_ok)
  ultimately show ?thesis by(auto intro: exec_meth.intros)
next
  case (exec_catch XCP D)
  let ?PC = "length ins + pc"
  note [simp] = \<open>xcp = \<lfloor>XCP\<rfloor>\<close>
    \<open>ta = \<epsilon>\<close> \<open>h' = h\<close> \<open>stk' = Addr XCP # drop (length stk - D) stk\<close> \<open>loc' = loc\<close> \<open>xcp' = None\<close>
  from \<open>match_ex_table P (cname_of h XCP) ?PC (xt @ shift (length ins) xt') = \<lfloor>(pc', D)\<rfloor>\<close> xt
  have "match_ex_table P (cname_of h XCP) pc xt' = \<lfloor>(pc' - length ins, D)\<rfloor>"
    by(auto simp add: match_ex_table_append dest: match_ex_table_shift_pcD match_ex_table_pcsD)
  with \<open>D \<le> length stk\<close> show ?thesis by(auto intro: exec_meth.intros)
qed

lemma exec_meth_drop:
  "\<lbrakk> exec_meth ci P (ins @ ins') (shift (length ins) xt) t h (stk, loc, (length ins + pc), xcp) ta h' (stk', loc', pc', xcp');
     jump_ok ins' 0 b \<rbrakk>
   \<Longrightarrow> exec_meth ci P ins' xt t h (stk, loc, pc, xcp) ta h' (stk', loc', (pc' - length ins), xcp')"
by(auto intro: exec_meth_drop_xt[where xt = "[]"])

lemma exec_meth_drop_xt_pc:
  assumes exec: "exec_meth ci P (ins @ ins') (xt @ shift (length ins) xt') t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  and pc: "pc \<ge> length ins"
  and pcs: "pcs xt \<subseteq> {..<length ins}"
  and jump: "jump_ok ins' 0 n'"
  shows "pc' \<ge> length ins"
using exec
proof(cases rule: exec_meth.cases)
  case exec_instr thus ?thesis using jump pc
    apply(cases "ins' ! (pc - length ins)")
    apply(simp_all add: split_beta nth_append split: if_split_asm sum.split_asm)
    apply(force split: extCallRet.splits simp add: min_def extRet2JVM_def dest: jump_ok_GotoD jump_ok_IfFalseD)+
    done
next
  case exec_catch thus ?thesis using pcs pc
    by(auto dest: match_ex_table_pcsD match_ex_table_shift_pcD simp add: match_ex_table_append)
qed

lemmas exec_meth_drop_pc = exec_meth_drop_xt_pc[where xt="[]", simplified]

definition exec_move ::
  "('addr, 'heap) check_instr \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr expr1
  \<Rightarrow> 'heap  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option)
  \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action
  \<Rightarrow> 'heap \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"
where "exec_move ci P t e \<equiv> exec_meth ci (compP2 P) (compE2 e) (compxE2 e 0 0) t"

definition exec_moves :: 
  "('addr, 'heap) check_instr \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr expr1 list
  \<Rightarrow> 'heap \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option)
  \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_thread_action
  \<Rightarrow> 'heap \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"
where "exec_moves ci P t es \<equiv> exec_meth ci (compP2 P) (compEs2 es) (compxEs2 es 0 0) t"

abbreviation exec_move_a
where "exec_move_a \<equiv> exec_move (Abs_check_instr check_instr')"

abbreviation exec_move_d
where "exec_move_d \<equiv> exec_move (Abs_check_instr check_instr)"

abbreviation exec_moves_a
where "exec_moves_a \<equiv> exec_moves (Abs_check_instr check_instr')"

abbreviation exec_moves_d
where "exec_moves_d \<equiv> exec_moves (Abs_check_instr check_instr)"

lemma exec_move_newArrayI:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (newA T\<lfloor>e\<rceil>) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_newArray:
  "pc < length (compE2 e) \<Longrightarrow> exec_move ci P t (newA T\<lfloor>e\<rceil>) h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
unfolding exec_move_def by(auto intro!: ext intro: exec_meth_take)

lemma exec_move_CastI:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (Cast T e) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_Cast:
  "pc < length (compE2 e) \<Longrightarrow> exec_move ci P t (Cast T e) h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
unfolding exec_move_def by(auto intro!: ext intro: exec_meth_take)

lemma exec_move_InstanceOfI:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (e instanceof T) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_InstanceOf:
  "pc < length (compE2 e) \<Longrightarrow> exec_move ci P t (e instanceof T) h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
unfolding exec_move_def by(auto intro!: ext intro: exec_meth_take)

lemma exec_move_BinOpI1:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (e \<guillemotleft>bop\<guillemotright> e') h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_BinOp1:
  "pc < length (compE2 e) \<Longrightarrow> exec_move ci P t (e \<guillemotleft>bop\<guillemotright> e') h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
unfolding exec_move_def
by(auto intro!: ext intro: exec_meth_take_xt simp add: compxE2_size_convs)

lemma exec_move_BinOpI2:
  assumes exec: "exec_move ci P t e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t (e1 \<guillemotleft>bop\<guillemotright> e2) h (stk @ [v], loc, length (compE2 e1) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e1) + pc', xcp')"
proof -
  from exec have "exec_meth ci (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_move_def .
  from exec_meth_stk_offer[OF this, where stk''="[v]"] show ?thesis
    by(fastforce split: bop.splits intro: append_exec_meth_xt simp add: exec_move_def compxE2_size_convs compxE2_stack_xlift_convs)
qed

lemma exec_move_LAssI:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (V := e) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_LAss:
  "pc < length (compE2 e) \<Longrightarrow> exec_move ci P t (V := e) h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
unfolding exec_move_def by(auto intro!: ext intro: exec_meth_take)

lemma exec_move_AAccI1:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (e\<lfloor>e'\<rceil>) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_AAcc1:
  "pc < length (compE2 e) \<Longrightarrow> exec_move ci P t (e\<lfloor>e'\<rceil>) h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
unfolding exec_move_def
by(auto intro!: ext intro: exec_meth_take_xt simp add: compxE2_size_convs)

lemma exec_move_AAccI2:
  assumes exec: "exec_move ci P t e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t (e1\<lfloor>e2\<rceil>) h (stk @ [v], loc, length (compE2 e1) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e1) + pc', xcp')"
proof -
  from exec have "exec_meth ci (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_move_def .
  from exec_meth_stk_offer[OF this, where stk''="[v]"] show ?thesis
    by(fastforce intro: append_exec_meth_xt simp add: exec_move_def compxE2_size_convs compxE2_stack_xlift_convs)
qed

lemma exec_move_AAssI1:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (e\<lfloor>e'\<rceil> := e'') h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_AAss1:
  assumes pc: "pc < length (compE2 e)"
  shows "exec_move ci P t (e\<lfloor>e'\<rceil> := e'') h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
  (is "?lhs = ?rhs")
proof(rule ext iffI)+
  fix ta h' s' assume "?rhs ta h' s'"
  thus "?lhs ta h' s'" by(rule exec_move_AAssI1)
next
  fix ta h' s' assume "?lhs ta h' s'"
  hence "exec_meth ci (compP2 P) (compE2 e @ compE2 e' @ compE2 e'' @ [AStore, Push Unit])
     (compxE2 e 0 0 @ shift (length (compE2 e)) (compxE2 e' 0 (Suc 0) @ compxE2 e'' (length (compE2 e')) (Suc (Suc 0)))) t
     h (stk, loc, pc, xcp) ta h' s'" by(simp add: exec_move_def shift_compxE2 ac_simps)
  thus "?rhs ta h' s'" unfolding exec_move_def using pc by(rule exec_meth_take_xt)
qed

lemma exec_move_AAssI2:
  assumes exec: "exec_move ci P t e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t (e1\<lfloor>e2\<rceil> := e3) h (stk @ [v], loc, length (compE2 e1) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e1) + pc', xcp')"
proof -
  from exec have "exec_meth ci (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_move_def .
  from exec_meth_stk_offer[OF this, where stk''="[v]", simplified stack_xlift_compxE2, simplified]
  have "exec_meth ci (compP2 P) (compE2 e2 @ compE2 e3 @ [AStore, Push Unit]) (compxE2 e2 0 (Suc 0) @ shift (length (compE2 e2)) (compxE2 e3 0 (Suc (Suc 0)))) t h (stk @ [v], loc, pc, xcp) ta h' (stk' @ [v], loc', pc', xcp')"
    by(rule exec_meth_append_xt)
  hence "exec_meth ci (compP2 P) (compE2 e1 @ compE2 e2 @ compE2 e3 @ [AStore, Push Unit]) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 0 (Suc 0) @ shift (length (compE2 e2)) (compxE2 e3 0 (Suc (Suc 0))))) t h (stk @ [v], loc, length (compE2 e1) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e1) + pc', xcp')"
    by(rule append_exec_meth_xt) auto
  thus ?thesis by(auto simp add: exec_move_def shift_compxE2 ac_simps)
qed

lemma exec_move_AAssI3:
  assumes exec: "exec_move ci P t e3 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t (e1\<lfloor>e2\<rceil> := e3) h (stk @ [v', v], loc, length (compE2 e1) + length (compE2 e2) + pc, xcp) ta h' (stk' @ [v', v], loc', length (compE2 e1) + length (compE2 e2) + pc', xcp')"
proof -
  from exec have "exec_meth ci (compP2 P) (compE2 e3) (compxE2 e3 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_move_def .
  from exec_meth_stk_offer[OF this, where stk''="[v', v]", simplified stack_xlift_compxE2, simplified]
  have "exec_meth ci (compP2 P) (compE2 e3 @ [AStore, Push Unit]) (compxE2 e3 0 (Suc (Suc 0))) t h (stk @ [v', v], loc, pc, xcp) ta h' (stk' @ [v', v], loc', pc', xcp')"
    by(rule exec_meth_append)
  hence "exec_meth ci (compP2 P) ((compE2 e1 @ compE2 e2) @ compE2 e3 @ [AStore, Push Unit]) 
                   ((compxE2 e1 0 0 @ compxE2 e2 (length (compE2 e1)) (Suc 0)) @ shift (length (compE2 e1 @ compE2 e2)) (compxE2 e3 0 (Suc (Suc 0)))) t h (stk @ [v', v], loc, length (compE2 e1 @ compE2 e2) + pc, xcp) ta h' (stk' @ [v', v], loc', length (compE2 e1 @ compE2 e2) + pc', xcp')"
    by(rule append_exec_meth_xt) auto
  thus ?thesis by(auto simp add: exec_move_def shift_compxE2 ac_simps)
qed

lemma exec_move_ALengthI:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (e\<bullet>length) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_ALength:
  "pc < length (compE2 e) \<Longrightarrow> exec_move ci P t (e\<bullet>length) h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
unfolding exec_move_def by(auto intro!: ext intro: exec_meth_take)

lemma exec_move_FAccI:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (e\<bullet>F{D}) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_FAcc:
  "pc < length (compE2 e) \<Longrightarrow> exec_move ci P t (e\<bullet>F{D}) h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
unfolding exec_move_def by(auto intro!: ext intro: exec_meth_take)

lemma exec_move_FAssI1:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (e\<bullet>F{D} := e') h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_FAss1:
  "pc < length (compE2 e) \<Longrightarrow> exec_move ci P t (e\<bullet>F{D} := e') h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
unfolding exec_move_def
by(auto intro!: ext intro: exec_meth_take_xt simp add: compxE2_size_convs)

lemma exec_move_FAssI2:
  assumes exec: "exec_move ci P t e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t (e1\<bullet>F{D} := e2) h (stk @ [v], loc, length (compE2 e1) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e1) + pc', xcp')"
proof -
  from exec have "exec_meth ci (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_move_def .
  from exec_meth_stk_offer[OF this, where stk''="[v]"] show ?thesis
    by(fastforce intro: append_exec_meth_xt simp add: exec_move_def compxE2_size_convs compxE2_stack_xlift_convs)
qed

lemma exec_move_CASI1:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_CAS1:
  assumes pc: "pc < length (compE2 e)"
  shows "exec_move ci P t (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
  (is "?lhs = ?rhs")
proof(rule ext iffI)+
  fix ta h' s' assume "?rhs ta h' s'"
  thus "?lhs ta h' s'" by(rule exec_move_CASI1)
next
  fix ta h' s' assume "?lhs ta h' s'"
  hence "exec_meth ci (compP2 P) (compE2 e @ compE2 e' @ compE2 e'' @ [CAS F D])
     (compxE2 e 0 0 @ shift (length (compE2 e)) (compxE2 e' 0 (Suc 0) @ compxE2 e'' (length (compE2 e')) (Suc (Suc 0)))) t
     h (stk, loc, pc, xcp) ta h' s'" by(simp add: exec_move_def shift_compxE2 ac_simps)
  thus "?rhs ta h' s'" unfolding exec_move_def using pc by(rule exec_meth_take_xt)
qed

lemma exec_move_CASI2:
  assumes exec: "exec_move ci P t e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) h (stk @ [v], loc, length (compE2 e1) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e1) + pc', xcp')"
proof -
  from exec have "exec_meth ci (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_move_def .
  from exec_meth_stk_offer[OF this, where stk''="[v]", simplified stack_xlift_compxE2, simplified]
  have "exec_meth ci (compP2 P) (compE2 e2 @ compE2 e3 @ [CAS F D]) (compxE2 e2 0 (Suc 0) @ shift (length (compE2 e2)) (compxE2 e3 0 (Suc (Suc 0)))) t h (stk @ [v], loc, pc, xcp) ta h' (stk' @ [v], loc', pc', xcp')"
    by(rule exec_meth_append_xt)
  hence "exec_meth ci (compP2 P) (compE2 e1 @ compE2 e2 @ compE2 e3 @ [CAS F D]) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 0 (Suc 0) @ shift (length (compE2 e2)) (compxE2 e3 0 (Suc (Suc 0))))) t h (stk @ [v], loc, length (compE2 e1) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e1) + pc', xcp')"
    by(rule append_exec_meth_xt) auto
  thus ?thesis by(auto simp add: exec_move_def shift_compxE2 ac_simps)
qed

lemma exec_move_CASI3:
  assumes exec: "exec_move ci P t e3 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) h (stk @ [v', v], loc, length (compE2 e1) + length (compE2 e2) + pc, xcp) ta h' (stk' @ [v', v], loc', length (compE2 e1) + length (compE2 e2) + pc', xcp')"
proof -
  from exec have "exec_meth ci (compP2 P) (compE2 e3) (compxE2 e3 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_move_def .
  from exec_meth_stk_offer[OF this, where stk''="[v', v]", simplified stack_xlift_compxE2, simplified]
  have "exec_meth ci (compP2 P) (compE2 e3 @ [CAS F D]) (compxE2 e3 0 (Suc (Suc 0))) t h (stk @ [v', v], loc, pc, xcp) ta h' (stk' @ [v', v], loc', pc', xcp')"
    by(rule exec_meth_append)
  hence "exec_meth ci (compP2 P) ((compE2 e1 @ compE2 e2) @ compE2 e3 @ [CAS F D]) 
                   ((compxE2 e1 0 0 @ compxE2 e2 (length (compE2 e1)) (Suc 0)) @ shift (length (compE2 e1 @ compE2 e2)) (compxE2 e3 0 (Suc (Suc 0)))) t h (stk @ [v', v], loc, length (compE2 e1 @ compE2 e2) + pc, xcp) ta h' (stk' @ [v', v], loc', length (compE2 e1 @ compE2 e2) + pc', xcp')"
    by(rule append_exec_meth_xt) auto
  thus ?thesis by(auto simp add: exec_move_def shift_compxE2 ac_simps)
qed

lemma exec_move_CallI1:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (e\<bullet>M(es)) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_Call1:
  "pc < length (compE2 e) \<Longrightarrow> exec_move ci P t (e\<bullet>M(es)) h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
unfolding exec_move_def
by(auto intro!: ext intro: exec_meth_take_xt simp add: compxEs2_size_convs)

lemma exec_move_CallI2:
  assumes exec: "exec_moves ci P t es h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t (e\<bullet>M(es)) h (stk @ [v], loc, length (compE2 e) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e) + pc', xcp')"
proof -
  from exec have "exec_meth ci (compP2 P) (compEs2 es) (compxEs2 es 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_moves_def .
  from exec_meth_stk_offer[OF this, where stk''="[v]"] show ?thesis
    by(fastforce intro: append_exec_meth_xt simp add: exec_move_def compxEs2_size_convs compxEs2_stack_xlift_convs)
qed

lemma exec_move_BlockNoneI:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t {V:T=None; e} h s ta h' s'"
unfolding exec_move_def by simp

lemma exec_move_BlockNone:
  "exec_move ci P t {V:T=None; e} = exec_move ci P t e"
unfolding exec_move_def by(simp)

lemma exec_move_BlockSomeI:
  assumes exec: "exec_move ci P t e h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t {V:T=\<lfloor>v\<rfloor>; e} h (stk, loc, Suc (Suc pc), xcp) ta h' (stk', loc', Suc (Suc pc'), xcp')"
proof -
  let ?ins = "[Push v, Store V]"
  from exec have "exec_meth ci (compP2 P) (compE2 e) (compxE2 e 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth ci (compP2 P) (?ins @ compE2 e) (shift (length ?ins) (compxE2 e 0 0)) t h (stk, loc, length ?ins + pc, xcp) ta h' (stk', loc', length ?ins + pc', xcp')"
    by(rule append_exec_meth) auto
  thus ?thesis by(simp add: exec_move_def shift_compxE2)
qed

lemma exec_move_BlockSome:
  "exec_move ci P t {V:T=\<lfloor>v\<rfloor>; e} h (stk, loc, Suc (Suc pc), xcp) ta h' (stk', loc', Suc (Suc pc'), xcp') =
   exec_move ci P t e h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')" (is "?lhs = ?rhs")
proof
  assume ?rhs thus ?lhs by(rule exec_move_BlockSomeI)
next
  let ?ins = "[Push v, Store V]"
  assume ?lhs
  hence "exec_meth ci (compP2 P) (?ins @ compE2 e) (shift (length ?ins) (compxE2 e 0 0)) t h (stk, loc, length ?ins + pc, xcp) ta h' (stk', loc', length ?ins + pc', xcp')"
    by(simp add: exec_move_def shift_compxE2)
  hence "exec_meth ci (compP2 P) (compE2 e) (compxE2 e 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', length ?ins + pc' - length ?ins, xcp')"
    by(rule exec_meth_drop) auto
  thus ?rhs by(simp add: exec_move_def)
qed

lemma exec_move_SyncI1:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (sync\<^bsub>V\<^esub> (e) e') h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_Sync1:
  assumes pc: "pc < length (compE2 e)"
  shows "exec_move ci P t (sync\<^bsub>V\<^esub> (e) e') h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
  (is "?lhs = ?rhs")
proof(rule ext iffI)+
  fix ta h' s'
  assume "?lhs ta h' s'"
  hence "exec_meth ci (compP2 P) (compE2 e @ Dup # Store V # MEnter # compE2 e' @ [Load V, MExit, Goto 4, Load V, MExit, ThrowExc])
                   (compxE2 e 0 0 @ shift (length (compE2 e)) (compxE2 e' 3 0 @ [(3, 3 + length (compE2 e'), None, 6 + length (compE2 e'), 0)]))
                   t h (stk, loc, pc, xcp) ta h' s'"
    by(simp add: shift_compxE2 ac_simps exec_move_def)
  thus "?rhs ta h' s'" unfolding exec_move_def using pc by(rule exec_meth_take_xt)
qed(rule exec_move_SyncI1)

lemma exec_move_SyncI2:
  assumes exec: "exec_move ci P t e h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t (sync\<^bsub>V\<^esub> (o') e) h (stk, loc, (Suc (Suc (Suc (length (compE2 o') + pc)))), xcp) ta h' (stk', loc', (Suc (Suc (Suc (length (compE2 o') + pc')))), xcp')"
proof -
  let ?e = "compE2 o' @ [Dup, Store V, MEnter]"
  let ?e' = "[Load V, MExit, Goto 4, Load V, MExit, ThrowExc]"
  from exec have "exec_meth ci (compP2 P) (compE2 e) (compxE2 e 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth ci (compP2 P) ((?e @ compE2 e) @ ?e') ((compxE2 o' 0 0 @ shift (length ?e) (compxE2 e 0 0)) @ [(length ?e, length ?e + length (compE2 e), None, length ?e + length (compE2 e) + 3, 0)]) t h (stk, loc, (length ?e + pc), xcp) ta h' (stk', loc', (length ?e + pc'), xcp')"
    by(rule exec_meth_append_xt[OF append_exec_meth_xt]) auto
  thus ?thesis by(simp add: eval_nat_numeral shift_compxE2 exec_move_def)
qed

lemma exec_move_SeqI1:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (e;;e') h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_Seq1:
  assumes pc: "pc < length (compE2 e)"
  shows "exec_move ci P t (e;;e') h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
  (is "?lhs = ?rhs")
proof(rule ext iffI)+
  fix ta h' s'
  assume "?lhs ta h' s'"
  hence "exec_meth ci (compP2 P) (compE2 e @ Pop # compE2 e') (compxE2 e 0 0 @ shift (length (compE2 e)) (compxE2 e' (Suc 0) 0)) t h (stk, loc, pc, xcp) ta h' s'"
    by(simp add: exec_move_def shift_compxE2)
  thus "?rhs ta h' s'" unfolding exec_move_def using pc by(rule exec_meth_take_xt)
qed(rule exec_move_SeqI1)

lemma exec_move_SeqI2:
  assumes exec: "exec_move ci P t e h (stk, loc, pc, xcp) ta h' (stk', loc', pc' ,xcp')"
  shows "exec_move ci P t (e';;e) h (stk, loc, (Suc (length (compE2 e') + pc)), xcp) ta h' (stk', loc', (Suc (length (compE2 e') + pc')), xcp')"
proof -
  from exec have "exec_meth ci (compP2 P) (compE2 e) (compxE2 e 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth ci (compP2 P) ((compE2 e' @ [Pop]) @ compE2 e) (compxE2 e' 0 0 @ shift (length (compE2 e' @ [Pop])) (compxE2 e 0 0)) t h (stk, loc, (length ((compE2 e') @ [Pop]) + pc), xcp) ta h' (stk', loc', (length ((compE2 e') @ [Pop]) + pc'), xcp')"
    by(rule append_exec_meth_xt) auto
  thus ?thesis by(simp add: shift_compxE2 exec_move_def)
qed

lemma exec_move_Seq2:
  assumes pc: "pc < length (compE2 e)"
  shows "exec_move ci P t (e';;e) h (stk, loc, Suc (length (compE2 e') + pc), xcp) ta
                                h' (stk', loc', Suc (length (compE2 e') + pc'), xcp') =
         exec_move ci P t e h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  (is "?lhs = ?rhs")
proof
  let ?E = "compE2 e' @ [Pop]"
  assume ?lhs
  hence "exec_meth ci (compP2 P) (?E @ compE2 e) (compxE2 e' 0 0 @ shift (length ?E) (compxE2 e 0 0)) t h (stk, loc, length ?E + pc, xcp) ta h' (stk', loc', length ?E + pc', xcp')"
    by(simp add: exec_move_def shift_compxE2)
  from exec_meth_drop_xt[OF this] show ?rhs unfolding exec_move_def by fastforce
qed(rule exec_move_SeqI2)

lemma exec_move_CondI1:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (if (e) e1 else e2) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_Cond1:
  assumes pc: "pc < length (compE2 e)"
  shows "exec_move ci P t (if (e) e1 else e2) h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
  (is "?lhs = ?rhs")
proof(rule ext iffI)+
  let ?E = "IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2"
  let ?xt = "compxE2 e1 (Suc 0) 0 @ compxE2 e2 (Suc (Suc (length (compE2 e1)))) 0"
  fix ta h' s'
  assume "?lhs ta h' s'"
  hence "exec_meth ci (compP2 P) (compE2 e @ ?E) (compxE2 e 0 0 @ shift (length (compE2 e)) ?xt) t h (stk, loc, pc, xcp) ta h' s'"
    by(simp add: exec_move_def shift_compxE2 ac_simps)
  thus "?rhs ta h' s'" unfolding exec_move_def using pc by(rule exec_meth_take_xt)
qed(rule exec_move_CondI1)

lemma exec_move_CondI2:
  assumes exec: "exec_move ci P t e1 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t (if (e) e1 else e2) h (stk, loc, (Suc (length (compE2 e) + pc)), xcp) ta h' (stk', loc', (Suc (length (compE2 e) + pc')), xcp')"
proof -
  from exec have "exec_meth ci (compP2 P) (compE2 e1) (compxE2 e1 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth ci (compP2 P) (((compE2 e @ [IfFalse (2 + int (length (compE2 e1)))]) @ compE2 e1) @ Goto (1 + int (length (compE2 e2))) # compE2 e2) ((compxE2 e 0 0 @ shift (length (compE2 e @ [IfFalse (2 + int (length (compE2 e1)))])) (compxE2 e1 0 0)) @ (compxE2 e2 (Suc (Suc (length (compE2 e) + length (compE2 e1)))) 0)) t h (stk, loc, (length (compE2 e @ [IfFalse (2 + int (length (compE2 e1)))]) + pc), xcp) ta h' (stk', loc', (length (compE2 e @ [IfFalse (2 + int (length (compE2 e1)))]) + pc'), xcp')"
    by -(rule exec_meth_append_xt, rule append_exec_meth_xt, auto)
  thus ?thesis by(simp add: shift_compxE2 exec_move_def)
qed

lemma exec_move_Cond2:
  assumes pc: "pc < length (compE2 e1)"
  shows "exec_move ci P t (if (e) e1 else e2) h (stk, loc, (Suc (length (compE2 e) + pc)), xcp) ta h' (stk', loc', (Suc (length (compE2 e) + pc')), xcp') = exec_move ci P t e1 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  (is "?lhs = ?rhs")
proof
  let ?E1 = "compE2 e @ [IfFalse (2 + int (length (compE2 e1)))]"
  let ?E2 = "Goto (1 + int (length (compE2 e2))) # compE2 e2"
  assume ?lhs
  hence "exec_meth ci (compP2 P) (?E1 @ compE2 e1 @ ?E2) (compxE2 e 0 0 @ shift (length ?E1) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 (Suc 0) 0))) t h (stk, loc, length ?E1 + pc, xcp) ta h' (stk', loc', length ?E1 + pc', xcp')"
    by(simp add: exec_move_def shift_compxE2 ac_simps)
  thus ?rhs unfolding exec_move_def
    by -(rule exec_meth_take_xt,drule exec_meth_drop_xt,auto simp add: pc)
qed(rule exec_move_CondI2)

lemma exec_move_CondI3:
  assumes exec: "exec_move ci P t e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t (if (e) e1 else e2) h (stk, loc, Suc (Suc (length (compE2 e) + length (compE2 e1) + pc)), xcp) ta h' (stk', loc', Suc (Suc (length (compE2 e) + length (compE2 e1) + pc')), xcp')"
proof -
  let ?E = "compE2 e @ IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ [Goto (1 + int (length (compE2 e2)))]"
  let ?xt = "compxE2 e 0 0 @ compxE2 e1 (Suc (length (compE2 e))) 0"
  from exec have "exec_meth ci (compP2 P) (compE2 e2) (compxE2 e2 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth ci (compP2 P) (?E @ compE2 e2) (?xt @ shift (length ?E) (compxE2 e2 0 0)) t h (stk, loc, length ?E + pc, xcp) ta h' (stk', loc', length ?E + pc', xcp')"
    by(rule append_exec_meth_xt) auto
  thus ?thesis by(simp add: shift_compxE2 exec_move_def)
qed

lemma exec_move_Cond3:
  "exec_move ci P t (if (e) e1 else e2) h (stk, loc, Suc (Suc (length (compE2 e) + length (compE2 e1) + pc)), xcp) ta
                                      h' (stk', loc', Suc (Suc (length (compE2 e) + length (compE2 e1) + pc')), xcp') =
   exec_move ci P t e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  (is "?lhs = ?rhs")
proof
  let ?E = "compE2 e @ IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ [Goto (1 + int (length (compE2 e2)))]"
  let ?xt = "compxE2 e 0 0 @ compxE2 e1 (Suc (length (compE2 e))) 0"
  assume ?lhs
  hence "exec_meth ci (compP2 P) (?E @ compE2 e2) (?xt @ shift (length ?E) (compxE2 e2 0 0)) t h (stk, loc, length ?E + pc, xcp) ta h' (stk', loc', length ?E + pc', xcp')"
    by(simp add: shift_compxE2 exec_move_def)
  thus ?rhs unfolding exec_move_def by -(drule exec_meth_drop_xt, auto)
qed(rule exec_move_CondI3)

lemma exec_move_WhileI1:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (while (e) e') h s ta h' s'"
unfolding exec_move_def by auto

lemma (in ab_group_add) uminus_minus_left_commute:
  "- a - (b + c) = - b - (a + c)"
  by (simp add: algebra_simps)

lemma exec_move_While1:
  assumes pc: "pc < length (compE2 e)"
  shows "exec_move ci P t (while (e) e') h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
  (is "?lhs = ?rhs")
proof(rule ext iffI)+
  let ?E = "IfFalse (3 + int (length (compE2 e'))) # compE2 e' @ [Pop, Goto (- int (length (compE2 e)) + (-2 - int (length (compE2 e')))), Push Unit]"
  let ?xt = "compxE2 e' (Suc 0) 0"
  fix ta h' s'
  assume "?lhs ta h' s'"
  then have "exec_meth ci (compP2 P) (compE2 e @ ?E) (compxE2 e 0 0 @ shift (length (compE2 e)) ?xt) t h (stk, loc, pc, xcp) ta h' s'"
    by (simp add: exec_move_def shift_compxE2 algebra_simps uminus_minus_left_commute)
  thus "?rhs ta h' s'" unfolding exec_move_def using pc by(rule exec_meth_take_xt)
qed(rule exec_move_WhileI1)

lemma exec_move_WhileI2:
  assumes exec: "exec_move ci P t e1 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t (while (e) e1) h (stk, loc, (Suc (length (compE2 e) + pc)), xcp) ta h' (stk', loc', (Suc (length (compE2 e) + pc')), xcp')"
proof -
  let ?E = "compE2 e @ [IfFalse (3 + int (length (compE2 e1)))]"
  let ?E' = "[Pop, Goto (- int (length (compE2 e)) + (-2 - int (length (compE2 e1)))), Push Unit]"
  from exec have "exec_meth ci (compP2 P) (compE2 e1) (compxE2 e1 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth ci (compP2 P) ((?E @ compE2 e1) @ ?E') (compxE2 e 0 0 @ shift (length ?E) (compxE2 e1 0 0)) t h (stk, loc, length ?E + pc, xcp) ta h' (stk', loc', length ?E + pc', xcp')"
    by -(rule exec_meth_append, rule append_exec_meth_xt, auto)
  thus ?thesis by (simp add: shift_compxE2 exec_move_def algebra_simps uminus_minus_left_commute)
qed

lemma exec_move_While2:
  assumes pc: "pc < length (compE2 e')"
  shows "exec_move ci P t (while (e) e') h (stk, loc, (Suc (length (compE2 e) + pc)), xcp) ta
                                    h' (stk', loc', (Suc (length (compE2 e) + pc')), xcp') =
         exec_move ci P t e' h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  (is "?lhs = ?rhs")
proof
  let ?E = "compE2 e @ [IfFalse (3 + int (length (compE2 e')))]"
  let ?E' = "[Pop, Goto (- int (length (compE2 e)) + (-2 - int (length (compE2 e')))), Push Unit]"
  assume ?lhs
  hence "exec_meth ci (compP2 P) ((?E @ compE2 e') @ ?E') (compxE2 e 0 0 @ shift (length ?E) (compxE2 e' 0 0)) t h (stk, loc, length ?E + pc, xcp) ta h' (stk', loc', length ?E + pc', xcp')"
    by(simp add: exec_move_def shift_compxE2 algebra_simps uminus_minus_left_commute)
  thus ?rhs unfolding exec_move_def using pc
    by -(drule exec_meth_take, simp, drule exec_meth_drop_xt, auto)
qed(rule exec_move_WhileI2)

lemma exec_move_ThrowI:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (throw e) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_Throw:
  "pc < length (compE2 e) \<Longrightarrow> exec_move ci P t (throw e) h (stk, loc, pc, xcp) = exec_move ci P t e h (stk, loc, pc, xcp)"
unfolding exec_move_def by(auto intro!: ext intro: exec_meth_take)

lemma exec_move_TryI1:
  "exec_move ci P t e h s ta h' s' \<Longrightarrow> exec_move ci P t (try e catch(C V) e') h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_TryI2:
  assumes exec: "exec_move ci P t e h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move ci P t (try e' catch(C V) e) h (stk, loc, Suc (Suc (length (compE2 e') + pc)), xcp) ta h' (stk', loc', Suc (Suc (length (compE2 e') + pc')), xcp')"
proof -
  let ?e = "compE2 e' @ [Goto (int(size (compE2 e))+2), Store V]"
  from exec have "exec_meth ci (compP2 P) (compE2 e) (compxE2 e 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth ci (compP2 P) ((?e @ compE2 e) @ []) ((compxE2 e' 0 0 @ shift (length ?e) (compxE2 e 0 0)) @ [(0, length (compE2 e'), \<lfloor>C\<rfloor>, Suc (length (compE2 e')), 0)]) t h (stk, loc, (length ?e + pc), xcp) ta h' (stk', loc', (length ?e + pc'), xcp')"
    by(rule exec_meth_append_xt[OF append_exec_meth_xt]) auto
  thus ?thesis by(simp add: eval_nat_numeral shift_compxE2 exec_move_def)
qed

lemma exec_move_Try2:
  "exec_move ci P t (try e catch(C V) e') h (stk, loc, Suc (Suc (length (compE2 e) + pc)), xcp) ta
                                     h' (stk', loc', Suc (Suc (length (compE2 e) + pc')), xcp') =
   exec_move ci P t e' h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  (is "?lhs = ?rhs")
proof
  let ?E = "compE2 e @ [Goto (int(size (compE2 e'))+2), Store V]"
  let ?xt = "[(0, length (compE2 e), \<lfloor>C\<rfloor>, Suc (length (compE2 e)), 0)]"
  assume lhs: ?lhs
  hence pc: "pc < length (compE2 e')"
    by(fastforce elim!: exec_meth.cases simp add: exec_move_def match_ex_table_append match_ex_entry dest: match_ex_table_pcsD)
  from lhs have "exec_meth ci (compP2 P) ((?E @ compE2 e') @ []) ((compxE2 e 0 0 @ shift (length ?E) (compxE2 e' 0 0)) @ ?xt) t h (stk, loc, length ?E + pc, xcp) ta h' (stk', loc', length ?E + pc', xcp')"
    by(simp add: exec_move_def shift_compxE2 ac_simps)
  thus ?rhs unfolding exec_move_def using pc
    by-(drule exec_meth_drop_xt[OF exec_meth_take_xt'], auto)
qed(rule exec_move_TryI2)

lemma exec_move_raise_xcp_pcD:
  "exec_move ci P t E h (stk, loc, pc, None) ta h' (stk', loc', pc', Some a) \<Longrightarrow> pc' = pc"
apply(cases "compE2 E ! pc")
apply(auto simp add: exec_move_def elim!: exec_meth.cases split: if_split_asm sum.split_asm)
apply(auto split: extCallRet.split_asm simp add: split_beta)
done


definition \<tau>exec_meth :: 
  "('addr, 'heap) check_instr \<Rightarrow> 'addr jvm_prog \<Rightarrow> 'addr instr list \<Rightarrow> ex_table \<Rightarrow> 'thread_id \<Rightarrow> 'heap
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option)
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"
where
  "\<tau>exec_meth ci P ins xt t h s s' \<longleftrightarrow> 
  exec_meth ci P ins xt t h s \<epsilon> h s' \<and> (snd (snd (snd s)) = None \<longrightarrow> \<tau>instr P h (fst s) (ins ! fst (snd (snd s))))"

abbreviation \<tau>exec_meth_a
where "\<tau>exec_meth_a \<equiv> \<tau>exec_meth (Abs_check_instr check_instr')"

abbreviation \<tau>exec_meth_d
where "\<tau>exec_meth_d \<equiv> \<tau>exec_meth (Abs_check_instr check_instr)"

lemma \<tau>exec_methI [intro]:
  "\<lbrakk> exec_meth ci P ins xt t h (stk, loc, pc, xcp) \<epsilon> h s'; xcp = None \<Longrightarrow> \<tau>instr P h stk (ins ! pc) \<rbrakk>
   \<Longrightarrow> \<tau>exec_meth ci P ins xt t h (stk, loc, pc, xcp) s'"
by(simp add: \<tau>exec_meth_def)

lemma \<tau>exec_methE [elim]:
  assumes "\<tau>exec_meth ci P ins xt t h s s'"
  obtains stk loc pc xcp
  where "s = (stk, loc, pc, xcp)"
  and "exec_meth ci P ins xt t h (stk, loc, pc, xcp) \<epsilon> h s'"
  and "xcp = None \<Longrightarrow> \<tau>instr P h stk (ins ! pc)"
using assms
by(cases s)(auto simp add: \<tau>exec_meth_def)

abbreviation \<tau>Exec_methr :: 
  "('addr, 'heap) check_instr \<Rightarrow> 'addr jvm_prog \<Rightarrow> 'addr instr list \<Rightarrow> ex_table \<Rightarrow> 'thread_id \<Rightarrow> 'heap 
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option)
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"
where
  "\<tau>Exec_methr ci P ins xt t h == (\<tau>exec_meth ci P ins xt t h)^**"

abbreviation \<tau>Exec_metht :: 
  "('addr, 'heap) check_instr \<Rightarrow> 'addr jvm_prog \<Rightarrow> 'addr instr list \<Rightarrow> ex_table \<Rightarrow> 'thread_id \<Rightarrow> 'heap
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option)
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"
where
  "\<tau>Exec_metht ci P ins xt t h == (\<tau>exec_meth ci P ins xt t h)^++"

abbreviation \<tau>Exec_methr_a
where "\<tau>Exec_methr_a \<equiv> \<tau>Exec_methr (Abs_check_instr check_instr')"

abbreviation \<tau>Exec_methr_d
where "\<tau>Exec_methr_d \<equiv> \<tau>Exec_methr (Abs_check_instr check_instr)"

abbreviation \<tau>Exec_metht_a
where "\<tau>Exec_metht_a \<equiv> \<tau>Exec_metht (Abs_check_instr check_instr')"

abbreviation \<tau>Exec_metht_d
where "\<tau>Exec_metht_d \<equiv> \<tau>Exec_metht (Abs_check_instr check_instr)"

lemma \<tau>Exec_methr_refl: "\<tau>Exec_methr ci P ins xt t h s s" ..

lemma \<tau>Exec_methr_step':
  "\<lbrakk> \<tau>Exec_methr ci P ins xt t h s (stk', loc', pc', xcp');
     \<tau>exec_meth ci P ins xt t h (stk', loc', pc', xcp') s' \<rbrakk>
  \<Longrightarrow> \<tau>Exec_methr ci P ins xt t h s s'"
by(rule rtranclp.rtrancl_into_rtrancl)

lemma \<tau>Exec_methr_step:
  "\<lbrakk> \<tau>Exec_methr ci P ins xt t h s (stk', loc', pc', xcp');
     exec_meth ci P ins xt t h (stk', loc', pc', xcp') \<epsilon> h s';
     xcp' = None \<Longrightarrow> \<tau>instr P h stk' (ins ! pc') \<rbrakk>
  \<Longrightarrow> \<tau>Exec_methr ci P ins xt t h s s'"
by(erule \<tau>Exec_methr_step')(rule \<tau>exec_methI)

lemmas \<tau>Exec_methr_intros = \<tau>Exec_methr_refl \<tau>Exec_methr_step
lemmas \<tau>Exec_methr1step = \<tau>Exec_methr_step[OF \<tau>Exec_methr_refl]
lemmas \<tau>Exec_methr2step = \<tau>Exec_methr_step[OF \<tau>Exec_methr_step, OF \<tau>Exec_methr_refl]
lemmas \<tau>Exec_methr3step = \<tau>Exec_methr_step[OF \<tau>Exec_methr_step, OF \<tau>Exec_methr_step, OF \<tau>Exec_methr_refl]

lemma \<tau>Exec_methr_cases [consumes 1, case_names refl step]:
  assumes "\<tau>Exec_methr ci P ins xt t h s s'"
  obtains "s = s'"
  | stk' loc' pc' xcp'
    where "\<tau>Exec_methr ci P ins xt t h s (stk', loc', pc', xcp')"
       "exec_meth ci P ins xt t h (stk', loc', pc', xcp') \<epsilon> h s'"
       "xcp' = None \<Longrightarrow> \<tau>instr P h stk' (ins ! pc')"
using assms
by(rule rtranclp.cases)(auto elim!: \<tau>exec_methE)

lemma \<tau>Exec_methr_induct [consumes 1, case_names refl step]:
  "\<lbrakk> \<tau>Exec_methr ci P ins xt t h s s';
     Q s;
     \<And>stk loc pc xcp s'. \<lbrakk> \<tau>Exec_methr ci P ins xt t h s (stk, loc, pc, xcp); exec_meth ci P ins xt t h (stk, loc, pc, xcp) \<epsilon> h s';
                          xcp = None \<Longrightarrow> \<tau>instr P h stk (ins ! pc); Q (stk, loc, pc, xcp) \<rbrakk> \<Longrightarrow> Q s' \<rbrakk>
  \<Longrightarrow> Q s'"
by(erule (1) rtranclp_induct)(blast elim: \<tau>exec_methE)

lemma \<tau>Exec_methr_trans: 
  "\<lbrakk> \<tau>Exec_methr ci P ins xt t h s s'; \<tau>Exec_methr ci P ins xt t h s' s'' \<rbrakk> \<Longrightarrow> \<tau>Exec_methr ci P ins xt t h s s''"
by(rule rtranclp_trans)

lemmas \<tau>Exec_meth_induct_split = \<tau>Exec_methr_induct[split_format (complete), consumes 1, case_names \<tau>Exec_refl \<tau>Exec_step]

lemma \<tau>Exec_methr_converse_cases [consumes 1, case_names refl step]:
  assumes "\<tau>Exec_methr ci P ins xt t h s s'"
  obtains "s = s'"
  | stk loc pc xcp s''
    where "s = (stk, loc, pc, xcp)"
       "exec_meth ci P ins xt t h (stk, loc, pc, xcp) \<epsilon> h s''"
       "xcp = None \<Longrightarrow> \<tau>instr P h stk (ins ! pc)"
       "\<tau>Exec_methr ci P ins xt t h s'' s'"
using assms
by(erule converse_rtranclpE)(blast elim: \<tau>exec_methE)

definition \<tau>exec_move :: 
  "('addr, 'heap) check_instr \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr expr1 \<Rightarrow> 'heap
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option)
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"
where
  "\<tau>exec_move ci P t e h =
  (\<lambda>(stk, loc, pc, xcp) s'. exec_move ci P t e h (stk, loc, pc, xcp) \<epsilon> h s' \<and> \<tau>move2 P h stk e pc xcp)"

definition \<tau>exec_moves :: 
  "('addr, 'heap) check_instr \<Rightarrow> 'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr expr1 list \<Rightarrow> 'heap
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option)
  \<Rightarrow> ('addr val list \<times> 'addr val list \<times> pc \<times> 'addr option) \<Rightarrow> bool"
where
  "\<tau>exec_moves ci P t es h =
   (\<lambda>(stk, loc, pc, xcp) s'. exec_moves ci P t es h (stk, loc, pc, xcp) \<epsilon> h s' \<and> \<tau>moves2 P h stk es pc xcp)"

lemma \<tau>exec_moveI:
  "\<lbrakk> exec_move ci P t e h (stk, loc, pc, xcp) \<epsilon> h s'; \<tau>move2 P h stk e pc xcp \<rbrakk> 
  \<Longrightarrow> \<tau>exec_move ci P t e h (stk, loc, pc, xcp) s'"
by(simp add: \<tau>exec_move_def)

lemma \<tau>exec_moveE:
  assumes "\<tau>exec_move ci P t e h (stk, loc, pc, xcp) s'"
  obtains "exec_move ci P t e h (stk, loc, pc, xcp) \<epsilon> h s'" "\<tau>move2 P h stk e pc xcp"
using assms by(simp add: \<tau>exec_move_def)

lemma \<tau>exec_movesI:
  "\<lbrakk> exec_moves ci P t es h (stk, loc, pc, xcp) \<epsilon> h s'; \<tau>moves2 P h stk es pc xcp \<rbrakk> 
  \<Longrightarrow> \<tau>exec_moves ci P t es h (stk, loc, pc, xcp) s'"
by(simp add: \<tau>exec_moves_def)

lemma \<tau>exec_movesE:
  assumes "\<tau>exec_moves ci P t es h (stk, loc, pc, xcp) s'"
  obtains "exec_moves ci P t es h (stk, loc, pc, xcp) \<epsilon> h s'" "\<tau>moves2 P h stk es pc xcp"
using assms by(simp add: \<tau>exec_moves_def)

lemma \<tau>exec_move_conv_\<tau>exec_meth:
  "\<tau>exec_move ci P t e = \<tau>exec_meth ci (compP2 P) (compE2 e) (compxE2 e 0 0) t"
by(auto simp add: \<tau>exec_move_def exec_move_def \<tau>move2_iff compP2_def intro!: ext \<tau>exec_methI elim!: \<tau>exec_methE)

lemma \<tau>exec_moves_conv_\<tau>exec_meth:
  "\<tau>exec_moves ci P t es = \<tau>exec_meth ci (compP2 P) (compEs2 es) (compxEs2 es 0 0) t"
by(auto simp add: \<tau>exec_moves_def exec_moves_def \<tau>moves2_iff compP2_def intro!: ext \<tau>exec_methI elim!: \<tau>exec_methE)

abbreviation \<tau>Exec_mover
where "\<tau>Exec_mover ci P t e h == (\<tau>exec_move ci P t e h)^**"

abbreviation \<tau>Exec_movet
where "\<tau>Exec_movet ci P t e h == (\<tau>exec_move ci P t e h)^++"

abbreviation \<tau>Exec_mover_a
where "\<tau>Exec_mover_a \<equiv> \<tau>Exec_mover (Abs_check_instr check_instr')"

abbreviation \<tau>Exec_mover_d
where "\<tau>Exec_mover_d \<equiv> \<tau>Exec_mover (Abs_check_instr check_instr)"

abbreviation \<tau>Exec_movet_a
where "\<tau>Exec_movet_a \<equiv> \<tau>Exec_movet (Abs_check_instr check_instr')"

abbreviation \<tau>Exec_movet_d
where "\<tau>Exec_movet_d \<equiv> \<tau>Exec_movet (Abs_check_instr check_instr)"

abbreviation \<tau>Exec_movesr
where "\<tau>Exec_movesr ci P t e h == (\<tau>exec_moves ci P t e h)^**"

abbreviation \<tau>Exec_movest
where "\<tau>Exec_movest ci P t e h == (\<tau>exec_moves ci P t e h)^++"

abbreviation \<tau>Exec_movesr_a
where "\<tau>Exec_movesr_a \<equiv> \<tau>Exec_movesr (Abs_check_instr check_instr')"

abbreviation \<tau>Exec_movesr_d
where "\<tau>Exec_movesr_d \<equiv> \<tau>Exec_movesr (Abs_check_instr check_instr)"

abbreviation \<tau>Exec_movest_a
where "\<tau>Exec_movest_a \<equiv> \<tau>Exec_movest (Abs_check_instr check_instr')"

abbreviation \<tau>Exec_movest_d
where "\<tau>Exec_movest_d \<equiv> \<tau>Exec_movest (Abs_check_instr check_instr)"

lemma \<tau>Execr_refl: "\<tau>Exec_mover ci P t e h s s"
by(rule rtranclp.rtrancl_refl)

lemma \<tau>Execsr_refl: "\<tau>Exec_movesr ci P t e h s s"
by(rule rtranclp.rtrancl_refl)

lemma \<tau>Execr_step: 
  "\<lbrakk> \<tau>Exec_mover ci P t e h s (stk', loc', pc', xcp');
     exec_move ci P t e h (stk', loc', pc', xcp') \<epsilon> h s';
     \<tau>move2 P h stk' e pc' xcp' \<rbrakk>
  \<Longrightarrow> \<tau>Exec_mover ci P t e h s s'"
by(rule rtranclp.rtrancl_into_rtrancl)(auto elim: \<tau>exec_moveI)

lemma \<tau>Execsr_step: 
  "\<lbrakk> \<tau>Exec_movesr ci P t es h s (stk', loc', pc', xcp');
     exec_moves ci P t es h (stk', loc', pc', xcp') \<epsilon> h s';
     \<tau>moves2 P h stk' es pc' xcp' \<rbrakk>
  \<Longrightarrow> \<tau>Exec_movesr ci P t es h s s'"
by(rule rtranclp.rtrancl_into_rtrancl)(auto elim: \<tau>exec_movesI)

lemma \<tau>Exect_step:
  "\<lbrakk> \<tau>Exec_movet ci P t e h s (stk', loc', pc', xcp');
     exec_move ci P t e h (stk', loc', pc', xcp') \<epsilon> h s';
     \<tau>move2 P h stk' e pc' xcp' \<rbrakk>
  \<Longrightarrow> \<tau>Exec_movet ci P t e h s s'"
by(rule tranclp.trancl_into_trancl)(auto intro: \<tau>exec_moveI)

lemma \<tau>Execst_step:
  "\<lbrakk> \<tau>Exec_movest ci P t es h s (stk', loc', pc', xcp');
     exec_moves ci P t es h (stk', loc', pc', xcp') \<epsilon> h s';
     \<tau>moves2 P h stk' es pc' xcp' \<rbrakk>
  \<Longrightarrow> \<tau>Exec_movest ci P t es h s s'"
by(rule tranclp.trancl_into_trancl)(auto intro: \<tau>exec_movesI)

lemmas \<tau>Execr1step = \<tau>Execr_step[OF \<tau>Execr_refl]
lemmas \<tau>Execr2step = \<tau>Execr_step[OF \<tau>Execr_step, OF \<tau>Execr_refl]
lemmas \<tau>Execr3step = \<tau>Execr_step[OF \<tau>Execr_step, OF \<tau>Execr_step, OF \<tau>Execr_refl]

lemmas \<tau>Execsr1step = \<tau>Execsr_step[OF \<tau>Execsr_refl]
lemmas \<tau>Execsr2step = \<tau>Execsr_step[OF \<tau>Execsr_step, OF \<tau>Execsr_refl]
lemmas \<tau>Execsr3step = \<tau>Execsr_step[OF \<tau>Execsr_step, OF \<tau>Execsr_step, OF \<tau>Execsr_refl]

lemma \<tau>Exect1step:
  "\<lbrakk> exec_move ci P t e h s \<epsilon> h s';
     \<tau>move2 P h (fst s) e (fst (snd (snd s))) (snd (snd (snd s))) \<rbrakk>
  \<Longrightarrow> \<tau>Exec_movet ci P t e h s s'"
by(rule tranclp.r_into_trancl)(cases s, auto intro: \<tau>exec_moveI)

lemmas \<tau>Exect2step = \<tau>Exect_step[OF \<tau>Exect1step]
lemmas \<tau>Exect3step = \<tau>Exect_step[OF \<tau>Exect_step, OF \<tau>Exect1step]

lemma \<tau>Execst1step:
  "\<lbrakk> exec_moves ci P t es h s \<epsilon> h s';
     \<tau>moves2 P h (fst s) es (fst (snd (snd s))) (snd (snd (snd s))) \<rbrakk>
  \<Longrightarrow> \<tau>Exec_movest ci P t es h s s'"
by(rule tranclp.r_into_trancl)(cases s, auto intro: \<tau>exec_movesI)

lemmas \<tau>Execst2step = \<tau>Execst_step[OF \<tau>Execst1step]
lemmas \<tau>Execst3step = \<tau>Execst_step[OF \<tau>Execst_step, OF \<tau>Execst1step]

lemma \<tau>Execr_induct [consumes 1, case_names refl step]:
  assumes major: "\<tau>Exec_mover ci P t e h (stk, loc, pc, xcp) (stk'', loc'', pc'', xcp'')"
  and refl: "Q stk loc pc xcp"
  and step: "\<And>stk' loc' pc' xcp' stk'' loc'' pc'' xcp''.
             \<lbrakk> \<tau>Exec_mover ci P t e h (stk, loc, pc, xcp) (stk', loc', pc', xcp');
               \<tau>exec_move ci P t e h (stk', loc', pc', xcp') (stk'', loc'', pc'', xcp''); Q stk' loc' pc' xcp' \<rbrakk>
             \<Longrightarrow> Q stk'' loc'' pc'' xcp''"
  shows "Q stk'' loc'' pc'' xcp''"
using major refl
by(rule rtranclp_induct4)(rule step)

lemma \<tau>Execsr_induct [consumes 1, case_names refl step]:
  assumes major: "\<tau>Exec_movesr ci P t es h (stk, loc, pc, xcp) (stk'', loc'', pc'', xcp'')"
  and refl: "Q stk loc pc xcp"
  and step: "\<And>stk' loc' pc' xcp' stk'' loc'' pc'' xcp''.
             \<lbrakk> \<tau>Exec_movesr ci P t es h (stk, loc, pc, xcp) (stk', loc', pc', xcp');
               \<tau>exec_moves ci P t es h (stk', loc', pc', xcp') (stk'', loc'', pc'', xcp''); Q stk' loc' pc' xcp' \<rbrakk>
             \<Longrightarrow> Q stk'' loc'' pc'' xcp''"
  shows "Q stk'' loc'' pc'' xcp''"
using major refl
by(rule rtranclp_induct4)(rule step)

lemma \<tau>Exect_induct [consumes 1, case_names base step]:
  assumes major: "\<tau>Exec_movet ci P t e h (stk, loc, pc, xcp) (stk'', loc'', pc'', xcp'')"
  and base: "\<And>stk' loc' pc' xcp'. \<tau>exec_move ci P t e h (stk, loc, pc, xcp) (stk', loc', pc', xcp') \<Longrightarrow> Q stk' loc' pc' xcp'"
  and step: "\<And>stk' loc' pc' xcp' stk'' loc'' pc'' xcp''.
             \<lbrakk> \<tau>Exec_movet ci P t e h (stk, loc, pc, xcp) (stk', loc', pc', xcp');
               \<tau>exec_move ci P t e h (stk', loc', pc', xcp') (stk'', loc'', pc'', xcp''); Q stk' loc' pc' xcp' \<rbrakk>
             \<Longrightarrow> Q stk'' loc'' pc'' xcp''"
  shows "Q stk'' loc'' pc'' xcp''"
using major
by(rule tranclp_induct4)(erule base step)+

lemma \<tau>Execst_induct [consumes 1, case_names base step]:
  assumes major: "\<tau>Exec_movest ci P t es h (stk, loc, pc, xcp) (stk'', loc'', pc'', xcp'')"
  and base: "\<And>stk' loc' pc' xcp'. \<tau>exec_moves ci P t es h (stk, loc, pc, xcp) (stk', loc', pc', xcp') \<Longrightarrow> Q stk' loc' pc' xcp'"
  and step: "\<And>stk' loc' pc' xcp' stk'' loc'' pc'' xcp''.
             \<lbrakk> \<tau>Exec_movest ci P t es h (stk, loc, pc, xcp) (stk', loc', pc', xcp');
               \<tau>exec_moves ci P t es h (stk', loc', pc', xcp') (stk'', loc'', pc'', xcp''); Q stk' loc' pc' xcp' \<rbrakk>
             \<Longrightarrow> Q stk'' loc'' pc'' xcp''"
  shows "Q stk'' loc'' pc'' xcp''"
using major
by(rule tranclp_induct4)(erule base step)+

lemma \<tau>Exec_mover_\<tau>Exec_methr:
  "\<tau>Exec_mover ci P t e = \<tau>Exec_methr ci (compP2 P) (compE2 e) (compxE2 e 0 0) t"
by(simp only: \<tau>exec_move_conv_\<tau>exec_meth)

lemma \<tau>Exec_movesr_\<tau>Exec_methr:
  "\<tau>Exec_movesr ci P t es = \<tau>Exec_methr ci (compP2 P) (compEs2 es) (compxEs2 es 0 0) t"
by(simp only: \<tau>exec_moves_conv_\<tau>exec_meth)

lemma \<tau>Exec_movet_\<tau>Exec_metht:
  "\<tau>Exec_movet ci P t e = \<tau>Exec_metht ci (compP2 P) (compE2 e) (compxE2 e 0 0) t"
by(simp only: \<tau>exec_move_conv_\<tau>exec_meth)

lemma \<tau>Exec_movest_\<tau>Exec_metht:
  "\<tau>Exec_movest ci P t es = \<tau>Exec_metht ci (compP2 P) (compEs2 es) (compxEs2 es 0 0) t"
by(simp only: \<tau>exec_moves_conv_\<tau>exec_meth)

lemma \<tau>Exec_mover_trans: 
  "\<lbrakk> \<tau>Exec_mover ci P t e h s s'; \<tau>Exec_mover ci P t e h s' s'' \<rbrakk> \<Longrightarrow> \<tau>Exec_mover ci P t e h s s''"
by(rule rtranclp_trans)

lemma \<tau>Exec_movesr_trans: 
  "\<lbrakk> \<tau>Exec_movesr ci P t es h s s'; \<tau>Exec_movesr ci P t es h s' s'' \<rbrakk> \<Longrightarrow> \<tau>Exec_movesr ci P t es h s s''"
by(rule rtranclp_trans)

lemma \<tau>Exec_movet_trans: 
  "\<lbrakk> \<tau>Exec_movet ci P t e h s s'; \<tau>Exec_movet ci P t e h s' s'' \<rbrakk> \<Longrightarrow> \<tau>Exec_movet ci P t e h s s''"
by(rule tranclp_trans)

lemma \<tau>Exec_movest_trans: 
  "\<lbrakk> \<tau>Exec_movest ci P t es h s s'; \<tau>Exec_movest ci P t es h s' s'' \<rbrakk> \<Longrightarrow> \<tau>Exec_movest ci P t es h s s''"
by(rule tranclp_trans)

lemma \<tau>exec_move_into_\<tau>exec_moves:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_moves ci P t (e # es) h s s'"
by(cases s)(auto elim!: \<tau>exec_moveE intro!: \<tau>exec_movesI simp add: exec_move_def exec_moves_def intro: \<tau>moves2Hd)

lemma \<tau>Exec_mover_\<tau>Exec_movesr:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_movesr ci P t (e # es) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl \<tau>exec_move_into_\<tau>exec_moves)+

lemma \<tau>Exec_movet_\<tau>Exec_movest:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movest ci P t (e # es) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl \<tau>exec_move_into_\<tau>exec_moves)+

lemma exec_moves_append: "exec_moves ci P t es h s ta h' s' \<Longrightarrow> exec_moves ci P t (es @ es') h s ta h' s'"
by(auto simp add: exec_moves_def)

lemma \<tau>exec_moves_append: "\<tau>exec_moves ci P t es h s s' \<Longrightarrow> \<tau>exec_moves ci P t (es @ es') h s s'"
by(cases s)(auto elim!: \<tau>exec_movesE intro!: \<tau>exec_movesI exec_moves_append)

lemma \<tau>Exec_movesr_append [intro]:
  "\<tau>Exec_movesr ci P t es h s s' \<Longrightarrow> \<tau>Exec_movesr ci P t (es @ es') h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl \<tau>exec_moves_append)+

lemma \<tau>Exec_movest_append [intro]:
  "\<tau>Exec_movest ci P t es h s s' \<Longrightarrow> \<tau>Exec_movest ci P t (es @ es') h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl \<tau>exec_moves_append)+

lemma append_exec_moves:
  assumes len: "length vs = length es'"
  and exec: "exec_moves ci P t es h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_moves ci P t (es' @ es) h ((stk @ vs), loc, (length (compEs2 es') + pc), xcp) ta h' ((stk' @ vs), loc', (length (compEs2 es') + pc'), xcp')"
proof -
  from exec have "exec_meth ci (compP2 P) (compEs2 es) (compxEs2 es 0 0) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_moves_def .
  hence "exec_meth ci (compP2 P) (compEs2 es) (stack_xlift (length vs) (compxEs2 es 0 0)) t h ((stk @ vs), loc, pc, xcp) ta h' ((stk' @ vs), loc', pc', xcp')" by(rule exec_meth_stk_offer)
  hence "exec_meth ci (compP2 P) (compEs2 es' @ compEs2 es) (compxEs2 es' 0 0 @ shift (length (compEs2 es')) (stack_xlift (length (vs)) (compxEs2 es 0 0))) t h ((stk @ vs), loc, (length (compEs2 es') + pc), xcp) ta h' ((stk' @ vs), loc', (length (compEs2 es') + pc'), xcp')"
    by(rule append_exec_meth_xt) auto
  thus ?thesis by(simp add: exec_moves_def stack_xlift_compxEs2 shift_compxEs2 len)
qed


lemma append_\<tau>exec_moves:
  "\<lbrakk> length vs = length es';
    \<tau>exec_moves ci P t es h (stk, loc, pc, xcp) (stk', loc', pc', xcp') \<rbrakk>
  \<Longrightarrow> \<tau>exec_moves ci P t (es' @ es) h ((stk @ vs), loc, (length (compEs2 es') + pc), xcp) ((stk' @ vs), loc', (length (compEs2 es') + pc'), xcp')"
by(auto elim!: \<tau>exec_movesE intro: \<tau>exec_movesI append_exec_moves \<tau>moves2_stk_append append_\<tau>moves2)

lemma append_\<tau>Exec_movesr:
  assumes len: "length vs = length es'"
  shows "\<tau>Exec_movesr ci P t es h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movesr ci P t (es' @ es) h ((stk @ vs), loc, (length (compEs2 es') + pc), xcp) ((stk' @ vs), loc', (length (compEs2 es') + pc'), xcp')"
by(induct rule: rtranclp_induct4)(blast intro: rtranclp.rtrancl_into_rtrancl append_\<tau>exec_moves[OF len])+

lemma append_\<tau>Exec_movest:
  assumes len: "length vs = length es'"
  shows "\<tau>Exec_movest ci P t es h  (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movest ci P t (es' @ es) h ((stk @ vs), loc, (length (compEs2 es') + pc), xcp)  ((stk' @ vs), loc', (length (compEs2 es') + pc'), xcp')"
by(induct rule: tranclp_induct4)(blast intro: tranclp.trancl_into_trancl append_\<tau>exec_moves[OF len])+


lemma NewArray_\<tau>execI:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (newA T\<lfloor>e\<rceil>) h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_newArrayI)

lemma Cast_\<tau>execI:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (Cast T e) h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_CastI)

lemma InstanceOf_\<tau>execI:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (e instanceof T) h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_InstanceOfI)

lemma BinOp_\<tau>execI1:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (e \<guillemotleft>bop\<guillemotright> e') h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_BinOpI1)

lemma BinOp_\<tau>execI2:
  "\<tau>exec_move ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (e \<guillemotleft>bop\<guillemotright> e') h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_BinOpI2 \<tau>move2_stk_append)

lemma LAss_\<tau>execI:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (V := e) h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_LAssI)

lemma AAcc_\<tau>execI1:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (e\<lfloor>i\<rceil>) h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_AAccI1)

lemma AAcc_\<tau>execI2:
  "\<tau>exec_move ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (e\<lfloor>e'\<rceil>) h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_AAccI2 \<tau>move2_stk_append)

lemma AAss_\<tau>execI1:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (e\<lfloor>i\<rceil> := e') h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_AAssI1)

lemma AAss_\<tau>execI2:
  "\<tau>exec_move ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (e\<lfloor>e'\<rceil> := e'') h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_AAssI2 \<tau>move2_stk_append)

lemma AAss_\<tau>execI3:
  "\<tau>exec_move ci P t e'' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (e\<lfloor>e'\<rceil> := e'') h ((stk @ [v, v']), loc, (length (compE2 e) + length (compE2 e') + pc), xcp) ((stk' @ [v, v']), loc', (length (compE2 e) + length (compE2 e') + pc'), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_AAssI3 \<tau>move2_stk_append)

lemma ALength_\<tau>execI:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (e\<bullet>length) h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_ALengthI)

lemma FAcc_\<tau>execI:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (e\<bullet>F{D}) h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_FAccI)

lemma FAss_\<tau>execI1:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (e\<bullet>F{D} := e') h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_FAssI1)

lemma FAss_\<tau>execI2:
  "\<tau>exec_move ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (e\<bullet>F{D} := e') h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_FAssI2 \<tau>move2_stk_append)

lemma CAS_\<tau>execI1:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_CASI1)

lemma CAS_\<tau>execI2:
  "\<tau>exec_move ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_CASI2 \<tau>move2_stk_append)

lemma CAS_\<tau>execI3:
  "\<tau>exec_move ci P t e'' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) h ((stk @ [v, v']), loc, (length (compE2 e) + length (compE2 e') + pc), xcp) ((stk' @ [v, v']), loc', (length (compE2 e) + length (compE2 e') + pc'), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_CASI3 \<tau>move2_stk_append)

lemma Call_\<tau>execI1:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (e\<bullet>M(es)) h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_CallI1)

lemma Call_\<tau>execI2:
  "\<tau>exec_moves ci P t es h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (e\<bullet>M(es)) h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(blast elim: \<tau>exec_movesE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_CallI2 \<tau>moves2_stk_append)

lemma Block_\<tau>execI_Some:
  "\<tau>exec_move ci P t e h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t {V:T=\<lfloor>v\<rfloor>; e} h (stk, loc, Suc (Suc pc), xcp) (stk', loc', Suc (Suc pc'), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_BlockSomeI)

lemma Block_\<tau>execI_None:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t {V:T=None; e} h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_BlockNoneI)

lemma Sync_\<tau>execI:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (sync\<^bsub>V\<^esub> (e) e') h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_SyncI1)

lemma Insync_\<tau>execI:
  "\<tau>exec_move ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (sync\<^bsub>V\<^esub> (e) e') h (stk, loc, Suc (Suc (Suc (length (compE2 e) + pc))), xcp) (stk', loc', Suc (Suc (Suc (length (compE2 e) + pc'))), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_SyncI2)

lemma Seq_\<tau>execI1:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (e;; e') h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_SeqI1)

lemma Seq_\<tau>execI2:
  "\<tau>exec_move ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (e;; e') h (stk, loc, Suc (length (compE2 e) + pc), xcp) (stk', loc', Suc (length (compE2 e) + pc'), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_SeqI2)

lemma Cond_\<tau>execI1:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (if (e) e' else e'') h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_CondI1)

lemma Cond_\<tau>execI2:
  "\<tau>exec_move ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (if (e) e' else e'') h (stk, loc, Suc (length (compE2 e) + pc), xcp) (stk', loc', Suc (length (compE2 e) + pc'), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_CondI2)

lemma Cond_\<tau>execI3:
  "\<tau>exec_move ci P t e'' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (if (e) e' else e'') h (stk, loc, Suc (Suc (length (compE2 e) + length (compE2 e') + pc)), xcp) (stk', loc', Suc (Suc (length (compE2 e) + length (compE2 e') + pc')), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_CondI3)

lemma While_\<tau>execI1:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (while (e) e') h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_WhileI1)

lemma While_\<tau>execI2:
  "\<tau>exec_move ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (while (e) e') h (stk, loc, Suc (length (compE2 e) + pc), xcp) (stk', loc', Suc (length (compE2 e) + pc'), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_WhileI2)

lemma Throw_\<tau>execI:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (throw e) h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_ThrowI)

lemma Try_\<tau>execI1:
  "\<tau>exec_move ci P t e h s s' \<Longrightarrow> \<tau>exec_move ci P t (try e catch(C V) e') h s s'"
by(cases s)(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_TryI1)

lemma Try_\<tau>execI2:
  "\<tau>exec_move ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>exec_move ci P t (try e catch(C V) e') h (stk, loc, Suc (Suc (length (compE2 e) + pc)), xcp) (stk', loc', Suc (Suc (length (compE2 e) + pc')), xcp')"
by(blast elim: \<tau>exec_moveE intro: \<tau>exec_moveI \<tau>move2_\<tau>moves2.intros exec_move_TryI2)



lemma NewArray_\<tau>ExecrI:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (newA T\<lfloor>e\<rceil>) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl NewArray_\<tau>execI)+

lemma Cast_\<tau>ExecrI:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (Cast T e) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Cast_\<tau>execI)+

lemma InstanceOf_\<tau>ExecrI:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (e instanceof T) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl InstanceOf_\<tau>execI)+

lemma BinOp_\<tau>ExecrI1:
  "\<tau>Exec_mover ci P t e1 h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (e1 \<guillemotleft>bop\<guillemotright> e2) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl BinOp_\<tau>execI1)+

lemma BinOp_\<tau>ExecrI2:
  "\<tau>Exec_mover ci P t e2 h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_mover ci P t (e \<guillemotleft>bop\<guillemotright> e2)  h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl BinOp_\<tau>execI2)+

lemma LAss_\<tau>ExecrI:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (V := e) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl LAss_\<tau>execI)+

lemma AAcc_\<tau>ExecrI1:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (e\<lfloor>i\<rceil>) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl AAcc_\<tau>execI1)+

lemma AAcc_\<tau>ExecrI2:
  "\<tau>Exec_mover ci P t i h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_mover ci P t (a\<lfloor>i\<rceil>) h ((stk @ [v]), loc, (length (compE2 a) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 a) + pc'), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl AAcc_\<tau>execI2)+

lemma AAss_\<tau>ExecrI1:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (e\<lfloor>i\<rceil> := e') h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl AAss_\<tau>execI1)+

lemma AAss_\<tau>ExecrI2:
  "\<tau>Exec_mover ci P t i h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_mover ci P t (a\<lfloor>i\<rceil> := e) h ((stk @ [v]), loc, (length (compE2 a) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 a) + pc'), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl AAss_\<tau>execI2)+

lemma AAss_\<tau>ExecrI3:
  "\<tau>Exec_mover ci P t e h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_mover ci P t (a\<lfloor>i\<rceil> := e) h ((stk @ [v, v']), loc, (length (compE2 a) + length (compE2 i) + pc), xcp) ((stk' @ [v, v']), loc', (length (compE2 a) + length (compE2 i) + pc'), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl AAss_\<tau>execI3)+

lemma ALength_\<tau>ExecrI:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (e\<bullet>length) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl ALength_\<tau>execI)+

lemma FAcc_\<tau>ExecrI:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (e\<bullet>F{D}) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl FAcc_\<tau>execI)+

lemma FAss_\<tau>ExecrI1:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (e\<bullet>F{D} := e') h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl FAss_\<tau>execI1)+

lemma FAss_\<tau>ExecrI2:
  "\<tau>Exec_mover ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_mover ci P t (e\<bullet>F{D} := e') h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl FAss_\<tau>execI2)+

lemma CAS_\<tau>ExecrI1:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl CAS_\<tau>execI1)+

lemma CAS_\<tau>ExecrI2:
  "\<tau>Exec_mover ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_mover ci P t (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl CAS_\<tau>execI2)+

lemma CAS_\<tau>ExecrI3:
  "\<tau>Exec_mover ci P t e'' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_mover ci P t (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) h ((stk @ [v, v']), loc, (length (compE2 e) + length (compE2 e') + pc), xcp) ((stk' @ [v, v']), loc', (length (compE2 e) + length (compE2 e') + pc'), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl CAS_\<tau>execI3)+

lemma Call_\<tau>ExecrI1:
  "\<tau>Exec_mover ci P t obj h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (obj\<bullet>M'(es)) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Call_\<tau>execI1)+

lemma Call_\<tau>ExecrI2:
  "\<tau>Exec_movesr ci P t es h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_mover ci P t (obj\<bullet>M'(es)) h ((stk @ [v]), loc, (length (compE2 obj) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 obj) + pc'), xcp')"
by(induct rule: \<tau>Execsr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Call_\<tau>execI2)+

lemma Block_\<tau>ExecrI_Some:
  "\<tau>Exec_mover ci P t e h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_mover ci P t {V:T=\<lfloor>v\<rfloor>; e} h (stk, loc, (Suc (Suc pc)), xcp) (stk', loc', (Suc (Suc pc')), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Block_\<tau>execI_Some)+

lemma Block_\<tau>ExecrI_None:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t {V:T=None; e} h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Block_\<tau>execI_None)+

lemma Sync_\<tau>ExecrI:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (sync\<^bsub>V\<^esub> (e) e') h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Sync_\<tau>execI)+

lemma Insync_\<tau>ExecrI:
  "\<tau>Exec_mover ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_mover ci P t (sync\<^bsub>V\<^esub> (e) e')  h (stk, loc, (Suc (Suc (Suc (length (compE2 e) + pc)))), xcp) (stk', loc', (Suc (Suc (Suc (length (compE2 e) + pc')))), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Insync_\<tau>execI)+

lemma Seq_\<tau>ExecrI1:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (e;;e') h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Seq_\<tau>execI1)+

lemma Seq_\<tau>ExecrI2:
  "\<tau>Exec_mover ci P t e h (stk, loc, pc, xcp) (stk', loc', pc' ,xcp') \<Longrightarrow>
   \<tau>Exec_mover ci P t (e';;e) h (stk, loc, (Suc (length (compE2 e') + pc)), xcp) (stk', loc', (Suc (length (compE2 e') + pc')), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Seq_\<tau>execI2)+

lemma Cond_\<tau>ExecrI1:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (if (e) e1 else e2) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Cond_\<tau>execI1)+

lemma Cond_\<tau>ExecrI2:
  "\<tau>Exec_mover ci P t e1  h (stk, loc, pc, xcp) (stk', loc', pc', xcp') \<Longrightarrow>
   \<tau>Exec_mover ci P t (if (e) e1 else e2)  h (stk, loc, (Suc (length (compE2 e) + pc)), xcp) (stk', loc', (Suc (length (compE2 e) + pc')), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Cond_\<tau>execI2)+

lemma Cond_\<tau>ExecrI3:
  "\<tau>Exec_mover ci P t e2  h (stk, loc ,pc, xcp) (stk', loc', pc', xcp') \<Longrightarrow>
   \<tau>Exec_mover ci P t (if (e) e1 else e2)  h (stk, loc, (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))), xcp)  (stk', loc', (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc'))), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Cond_\<tau>execI3)+

lemma While_\<tau>ExecrI1:
  "\<tau>Exec_mover ci P t c h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (while (c) e) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl While_\<tau>execI1)+

lemma While_\<tau>ExecrI2:
  "\<tau>Exec_mover ci P t E h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_mover ci P t (while (c) E)  h (stk, loc ,(Suc (length (compE2 c) + pc)), xcp) (stk', loc', (Suc (length (compE2 c) + pc')), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl While_\<tau>execI2)+

lemma Throw_\<tau>ExecrI:
  "\<tau>Exec_mover ci P t e h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (throw e) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Throw_\<tau>execI)+

lemma Try_\<tau>ExecrI1:
  "\<tau>Exec_mover ci P t E h s s' \<Longrightarrow> \<tau>Exec_mover ci P t (try E catch(C' V) e) h s s'"
by(induct rule: rtranclp_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Try_\<tau>execI1)+

lemma Try_\<tau>ExecrI2:
  "\<tau>Exec_mover ci P t e h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_mover ci P t (try E catch(C' V) e)  h (stk, loc, (Suc (Suc (length (compE2 E) + pc))), xcp)  (stk', loc', (Suc (Suc (length (compE2 E) + pc'))), xcp')"
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl Try_\<tau>execI2)+


lemma NewArray_\<tau>ExectI:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (newA T\<lfloor>e\<rceil>) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl NewArray_\<tau>execI)+

lemma Cast_\<tau>ExectI:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (Cast T e) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl Cast_\<tau>execI)+

lemma InstanceOf_\<tau>ExectI:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (e instanceof T) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl InstanceOf_\<tau>execI)+

lemma BinOp_\<tau>ExectI1:
  "\<tau>Exec_movet ci P t e1 h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (e1 \<guillemotleft>bop\<guillemotright> e2) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl BinOp_\<tau>execI1)+

lemma BinOp_\<tau>ExectI2:
  "\<tau>Exec_movet ci P t e2 h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movet ci P t (e \<guillemotleft>bop\<guillemotright> e2)  h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl BinOp_\<tau>execI2)+

lemma LAss_\<tau>ExectI:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (V := e) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl LAss_\<tau>execI)+

lemma AAcc_\<tau>ExectI1:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (e\<lfloor>i\<rceil>) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl AAcc_\<tau>execI1)+

lemma AAcc_\<tau>ExectI2:
  "\<tau>Exec_movet ci P t i h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movet ci P t (a\<lfloor>i\<rceil>) h ((stk @ [v]), loc, (length (compE2 a) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 a) + pc'), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl AAcc_\<tau>execI2)+

lemma AAss_\<tau>ExectI1:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (e\<lfloor>i\<rceil> := e') h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl AAss_\<tau>execI1)+

lemma AAss_\<tau>ExectI2:
  "\<tau>Exec_movet ci P t i h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movet ci P t (a\<lfloor>i\<rceil> := e) h ((stk @ [v]), loc, (length (compE2 a) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 a) + pc'), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl AAss_\<tau>execI2)+

lemma AAss_\<tau>ExectI3:
  "\<tau>Exec_movet ci P t e h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movet ci P t (a\<lfloor>i\<rceil> := e) h ((stk @ [v, v']), loc, (length (compE2 a) + length (compE2 i) + pc), xcp) ((stk' @ [v, v']), loc', (length (compE2 a) + length (compE2 i) + pc'), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl AAss_\<tau>execI3)+

lemma ALength_\<tau>ExectI:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (e\<bullet>length) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl ALength_\<tau>execI)+

lemma FAcc_\<tau>ExectI:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (e\<bullet>F{D}) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl FAcc_\<tau>execI)+

lemma FAss_\<tau>ExectI1:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (e\<bullet>F{D} := e') h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl FAss_\<tau>execI1)+

lemma FAss_\<tau>ExectI2:
  "\<tau>Exec_movet ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movet ci P t (e\<bullet>F{D} := e') h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl FAss_\<tau>execI2)+

lemma CAS_\<tau>ExectI1:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl CAS_\<tau>execI1)+

lemma CAS_\<tau>ExectI2:
  "\<tau>Exec_movet ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movet ci P t (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl CAS_\<tau>execI2)+

lemma CAS_\<tau>ExectI3:
  "\<tau>Exec_movet ci P t e'' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movet ci P t (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) h ((stk @ [v, v']), loc, (length (compE2 e) + length (compE2 e') + pc), xcp) ((stk' @ [v, v']), loc', (length (compE2 e) + length (compE2 e') + pc'), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl CAS_\<tau>execI3)+

lemma Call_\<tau>ExectI1:
  "\<tau>Exec_movet ci P t obj h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (obj\<bullet>M'(es)) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl Call_\<tau>execI1)+

lemma Call_\<tau>ExectI2:
  "\<tau>Exec_movest ci P t es h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movet ci P t (obj\<bullet>M'(es)) h ((stk @ [v]), loc, (length (compE2 obj) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 obj) + pc'), xcp')"
by(induct rule: \<tau>Execst_induct)(blast intro: tranclp.trancl_into_trancl Call_\<tau>execI2)+

lemma Block_\<tau>ExectI_Some:
  "\<tau>Exec_movet ci P t e h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movet ci P t {V:T=\<lfloor>v\<rfloor>; e} h (stk, loc, (Suc (Suc pc)), xcp) (stk', loc', (Suc (Suc pc')), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl Block_\<tau>execI_Some)+

lemma Block_\<tau>ExectI_None:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t {V:T=None; e} h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl Block_\<tau>execI_None)+

lemma Sync_\<tau>ExectI:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (sync\<^bsub>V\<^esub> (e) e') h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl Sync_\<tau>execI)+

lemma Insync_\<tau>ExectI:
  "\<tau>Exec_movet ci P t e' h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movet ci P t (sync\<^bsub>V\<^esub> (e) e')  h (stk, loc, (Suc (Suc (Suc (length (compE2 e) + pc)))), xcp) (stk', loc', (Suc (Suc (Suc (length (compE2 e) + pc')))), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl Insync_\<tau>execI)+

lemma Seq_\<tau>ExectI1:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (e;;e') h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl Seq_\<tau>execI1)+

lemma Seq_\<tau>ExectI2:
  "\<tau>Exec_movet ci P t e h (stk, loc, pc, xcp) (stk', loc', pc' ,xcp') \<Longrightarrow>
   \<tau>Exec_movet ci P t (e';;e) h (stk, loc, (Suc (length (compE2 e') + pc)), xcp) (stk', loc', (Suc (length (compE2 e') + pc')), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl Seq_\<tau>execI2)+

lemma Cond_\<tau>ExectI1:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (if (e) e1 else e2) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl Cond_\<tau>execI1)+

lemma Cond_\<tau>ExectI2:
  "\<tau>Exec_movet ci P t e1  h (stk, loc, pc, xcp) (stk', loc', pc', xcp') \<Longrightarrow>
   \<tau>Exec_movet ci P t (if (e) e1 else e2)  h (stk, loc, (Suc (length (compE2 e) + pc)), xcp) (stk', loc', (Suc (length (compE2 e) + pc')), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl Cond_\<tau>execI2)+

lemma Cond_\<tau>ExectI3:
  "\<tau>Exec_movet ci P t e2  h (stk, loc ,pc, xcp) (stk', loc', pc', xcp') \<Longrightarrow>
   \<tau>Exec_movet ci P t (if (e) e1 else e2)  h (stk, loc, (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))), xcp)  (stk', loc', (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc'))), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl Cond_\<tau>execI3)+

lemma While_\<tau>ExectI1:
  "\<tau>Exec_movet ci P t c h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (while (c) e) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl While_\<tau>execI1)+

lemma While_\<tau>ExectI2:
  "\<tau>Exec_movet ci P t E h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movet ci P t (while (c) E)  h (stk, loc ,(Suc (length (compE2 c) + pc)), xcp) (stk', loc', (Suc (length (compE2 c) + pc')), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl While_\<tau>execI2)+

lemma Throw_\<tau>ExectI:
  "\<tau>Exec_movet ci P t e h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (throw e) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl Throw_\<tau>execI)+

lemma Try_\<tau>ExectI1:
  "\<tau>Exec_movet ci P t E h s s' \<Longrightarrow> \<tau>Exec_movet ci P t (try E catch(C' V) e) h s s'"
by(induct rule: tranclp_induct)(blast intro: tranclp.trancl_into_trancl Try_\<tau>execI1)+

lemma Try_\<tau>ExectI2:
  "\<tau>Exec_movet ci P t e h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_movet ci P t (try E catch(C' V) e)  h (stk, loc, (Suc (Suc (length (compE2 E) + pc))), xcp)  (stk', loc', (Suc (Suc (length (compE2 E) + pc'))), xcp')"
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl Try_\<tau>execI2)+

lemma \<tau>Exec_movesr_map_Val:
  "\<tau>Exec_movesr_a P t (map Val vs) h ([], xs, 0, None) ((rev vs), xs, (length (compEs2 (map Val vs))), None)"
proof(induct vs arbitrary: pc stk Ts rule: rev_induct)
  case Nil thus ?case by(auto)
next
  case (snoc v vs')
  let ?E = "compEs2 (map Val vs')"
  from snoc have "\<tau>Exec_movesr_a P t (map Val (vs' @ [v])) h ([], xs, 0, None) ((rev vs'), xs, (length ?E), None)"
    by auto
  also {
    have "exec_meth_a (compP2 P) (?E @ [Push v]) (compxEs2 (map Val vs') 0 0 @ shift (length ?E) []) t h ((rev vs'), xs, (length ?E + 0), None) \<epsilon> h ((v # rev vs'), xs, (length ?E + Suc 0), None)"
      by -(rule append_exec_meth_xt, auto simp add: exec_meth_instr)
    moreover have "\<tau>moves2 (compP2 P) h (rev vs') (map Val vs' @ [Val v]) (length (compEs2 (map Val vs')) + 0) None"
      by(rule append_\<tau>moves2 \<tau>moves2Hd \<tau>move2Val)+
    ultimately have "\<tau>Exec_movesr_a P t (map Val (vs' @ [v])) h ((rev vs'), xs, (length ?E), None) ((rev (vs' @ [v])), xs, (length (compEs2 (map Val (vs' @ [v])))), None)"
      by -(rule \<tau>Execsr1step, auto simp add: exec_moves_def compP2_def) }
  finally show ?case .
qed

lemma \<tau>Exec_mover_blocks1 [simp]:
  "\<tau>Exec_mover ci P t (blocks1 n Ts body) h s s' = \<tau>Exec_mover ci P t body h s s'"
by(simp add: \<tau>exec_move_conv_\<tau>exec_meth)

lemma \<tau>Exec_movet_blocks1 [simp]:
  "\<tau>Exec_movet ci P t (blocks1 n Ts body) h s s' = \<tau>Exec_movet ci P t body h s s'"
by(simp add: \<tau>exec_move_conv_\<tau>exec_meth)


definition \<tau>exec_1 :: "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> bool"
  where "\<tau>exec_1 P t \<sigma> \<sigma>' \<longleftrightarrow> exec_1 P t \<sigma> \<epsilon> \<sigma>' \<and> \<tau>Move2 P \<sigma>"

lemma \<tau>exec_1I [intro]:
  "\<lbrakk> exec_1 P t \<sigma> \<epsilon> \<sigma>'; \<tau>Move2 P \<sigma> \<rbrakk> \<Longrightarrow> \<tau>exec_1 P t \<sigma> \<sigma>'"
by(simp add: \<tau>exec_1_def)

lemma \<tau>exec_1E [elim]:
  assumes "\<tau>exec_1 P t \<sigma> \<sigma>'"
  obtains "exec_1 P t \<sigma> \<epsilon> \<sigma>'" "\<tau>Move2 P \<sigma>"
using assms by(auto simp add: \<tau>exec_1_def)

abbreviation \<tau>Exec_1r :: "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> bool"
where "\<tau>Exec_1r P t == (\<tau>exec_1 P t)^**"

abbreviation \<tau>Exec_1t :: "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> bool"
where "\<tau>Exec_1t P t == (\<tau>exec_1 P t)^++"

definition \<tau>exec_1_d :: "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> bool"
where "\<tau>exec_1_d P t \<sigma> \<sigma>' \<longleftrightarrow> exec_1 P t \<sigma> \<epsilon> \<sigma>' \<and> \<tau>Move2 P \<sigma> \<and> check P \<sigma>"

lemma \<tau>exec_1_dI [intro]:
  "\<lbrakk> exec_1 P t \<sigma> \<epsilon> \<sigma>'; check P \<sigma>; \<tau>Move2 P \<sigma> \<rbrakk> \<Longrightarrow> \<tau>exec_1_d P t \<sigma> \<sigma>'"
by(simp add: \<tau>exec_1_d_def)

lemma \<tau>exec_1_dE [elim]:
  assumes "\<tau>exec_1_d P t \<sigma> \<sigma>'"
  obtains "exec_1 P t \<sigma> \<epsilon> \<sigma>'" "check P \<sigma>" "\<tau>Move2 P \<sigma>"
using assms by(auto simp add: \<tau>exec_1_d_def)

abbreviation \<tau>Exec_1_dr :: "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> bool"
where "\<tau>Exec_1_dr P t == (\<tau>exec_1_d P t)^**"

abbreviation \<tau>Exec_1_dt :: "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> bool"
where "\<tau>Exec_1_dt P t == (\<tau>exec_1_d P t)^++"

declare compxE2_size_convs[simp del] compxEs2_size_convs[simp del]
declare compxE2_stack_xlift_convs[simp del] compxEs2_stack_xlift_convs[simp del]

lemma exec_instr_frs_offer:
  "(ta, xcp', h', (stk', loc', C, M, pc') # frs) \<in> exec_instr ins P t h stk loc C M pc frs
  \<Longrightarrow> (ta, xcp', h', (stk', loc', C, M, pc') # frs @ frs') \<in> exec_instr ins P t h stk loc C M pc (frs @ frs')"
apply(cases ins)
apply(simp_all add: nth_append split_beta split: if_split_asm sum.split_asm)
apply(force split: extCallRet.split_asm simp add: extRet2JVM_def)+
done

lemma check_instr_frs_offer:
  "\<lbrakk> check_instr ins P h stk loc C M pc frs; ins \<noteq> Return \<rbrakk>
  \<Longrightarrow> check_instr ins P h stk loc C M pc (frs @ frs')"
by(cases ins)(simp_all split: if_split_asm)

lemma exec_instr_CM_change:
  "(ta, xcp', h', (stk', loc', C, M, pc') # frs) \<in> exec_instr ins P t h stk loc C M pc frs
  \<Longrightarrow> (ta, xcp', h', (stk', loc', C', M', pc') # frs) \<in> exec_instr ins P t h stk loc C' M' pc frs"
apply(cases ins)
apply(simp_all add: nth_append split_beta neq_Nil_conv split: if_split_asm sum.split_asm)
apply(force split: extCallRet.split_asm simp add: extRet2JVM_def)+
done

lemma check_instr_CM_change:
  "\<lbrakk> check_instr ins P h stk loc C M pc frs; ins \<noteq> Return \<rbrakk>
  \<Longrightarrow> check_instr ins P h stk loc C' M' pc frs"
by(cases ins)(simp_all split: if_split_asm)

lemma exec_move_exec_1:
  assumes exec: "exec_move ci P t body h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  and sees: "P \<turnstile> C sees M : Ts\<rightarrow>T = \<lfloor>body\<rfloor> in D"
  shows "exec_1 (compP2 P) t (xcp, h, (stk, loc, C, M, pc) # frs) ta (xcp', h', (stk', loc', C, M, pc') # frs)"
using exec unfolding exec_move_def
proof(cases)
  case exec_instr
  note [simp] = \<open>xcp = None\<close>
    and exec = \<open>(ta, xcp', h', [(stk', loc', undefined, undefined, pc')])
                \<in> exec_instr (compE2 body ! pc) (compP2 P) t h stk loc undefined undefined pc []\<close>
  from exec have "(ta, xcp', h', [(stk', loc', C, M, pc')])
                \<in> exec_instr (compE2 body ! pc) (compP2 P) t h stk loc C M pc []"
    by(rule exec_instr_CM_change)
  from exec_instr_frs_offer[OF this, of frs]
  have "(ta, xcp', h', (stk', loc', C, M, pc') # frs)
        \<in> exec_instr (compE2 body ! pc) (compP2 P) t h stk loc C M pc frs" by simp
  with sees \<open>pc < length (compE2 body)\<close> show ?thesis
    by(simp add: exec_1_iff compP2_def compMb2_def nth_append)
next
  case exec_catch
  thus ?thesis using sees_method_compP[OF sees, of "\<lambda>C M Ts T. compMb2"]
    by(simp add: exec_1_iff compMb2_def compP2_def)
qed

lemma \<tau>exec_move_\<tau>exec_1:
  assumes exec: "\<tau>exec_move ci P t body h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
  and sees: "P \<turnstile> C sees M : Ts\<rightarrow>T = \<lfloor>body\<rfloor> in D"
  shows "\<tau>exec_1 (compP2 P) t (xcp, h, (stk, loc, C, M, pc) # frs) (xcp', h, (stk', loc', C, M, pc') # frs)"
proof(rule \<tau>exec_1I)
  from exec obtain exec': "exec_move ci P t body h (stk, loc, pc, xcp) \<epsilon> h (stk', loc', pc', xcp')"
    and \<tau>: "\<tau>move2 P h stk body pc xcp" by(rule \<tau>exec_moveE)
  have "exec_1 (compP2 P) t (xcp, h, (stk, loc, C, M, pc) # frs) \<epsilon> (xcp', h, (stk', loc', C, M, pc') # frs)"
    using exec' sees by(rule exec_move_exec_1)
  thus "compP2 P,t \<turnstile> (xcp, h, (stk, loc, C, M, pc) # frs) -\<epsilon>-jvm\<rightarrow> (xcp', h, (stk', loc', C, M, pc') # frs)" by auto
  { fix a
    assume [simp]: "xcp = \<lfloor>a\<rfloor>" 
    from sees_method_compP[OF sees, of "\<lambda>C M Ts T. compMb2"]
    have "ex_table_of (compP2 P) C M = compxE2 body 0 0" by(simp add: compP2_def compMb2_def)
    hence "match_ex_table (compP2 P) (cname_of h a) pc (ex_table_of (compP2 P) C M) \<noteq> None" "pc < length (compE2 body)"
      using exec' sees by(auto simp add: exec_move_def elim: exec_meth.cases) }
  with \<tau> sees sees_method_compP[OF sees, of "\<lambda>C M Ts T. compMb2"]
  show "\<tau>Move2 (compP2 P) (xcp, h, (stk, loc, C, M, pc) # frs)" 
    unfolding \<tau>Move2_compP2[OF sees] by(fastforce simp add: compP2_def compMb2_def)
qed

lemma \<tau>Exec_mover_\<tau>Exec_1r:
  assumes move: "\<tau>Exec_mover ci P t body h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
  and sees: "P \<turnstile> C sees M : Ts\<rightarrow>T = \<lfloor>body\<rfloor> in D"
  shows "\<tau>Exec_1r (compP2 P) t (xcp, h, (stk, loc, C, M, pc) # frs') (xcp', h, (stk', loc', C, M, pc') # frs')"
using move
by(induct rule: \<tau>Execr_induct)(blast intro: rtranclp.rtrancl_into_rtrancl \<tau>exec_move_\<tau>exec_1[OF _ sees])+

lemma \<tau>Exec_movet_\<tau>Exec_1t:
  assumes move: "\<tau>Exec_movet ci P t body h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
  and sees: "P \<turnstile> C sees M : Ts\<rightarrow>T = \<lfloor>body\<rfloor> in D"
  shows "\<tau>Exec_1t (compP2 P) t (xcp, h, (stk, loc, C, M, pc) # frs') (xcp', h, (stk', loc', C, M, pc') # frs')"
using move
by(induct rule: \<tau>Exect_induct)(blast intro: tranclp.trancl_into_trancl \<tau>exec_move_\<tau>exec_1[OF _ sees])+

lemma \<tau>Exec_1r_rtranclpD:
  "\<tau>Exec_1r P t (xcp, h, frs) (xcp', h', frs')
  \<Longrightarrow> (\<lambda>((xcp, frs), h) ((xcp', frs'), h'). exec_1 P t (xcp, h, frs) \<epsilon> (xcp', h', frs') \<and> \<tau>Move2 P (xcp, h, frs))^** ((xcp, frs), h) ((xcp', frs'), h')"
by(induct rule: rtranclp_induct3)(fastforce intro: rtranclp.rtrancl_into_rtrancl)+

lemma \<tau>Exec_1t_rtranclpD:
  "\<tau>Exec_1t P t (xcp, h, frs) (xcp', h', frs')
  \<Longrightarrow> (\<lambda>((xcp, frs), h) ((xcp', frs'), h'). exec_1 P t (xcp, h, frs) \<epsilon> (xcp', h', frs') \<and> \<tau>Move2 P (xcp, h, frs))^++ ((xcp, frs), h) ((xcp', frs'), h')"
by(induct rule: tranclp_induct3)(fastforce intro: tranclp.trancl_into_trancl)+

lemma exec_meth_length_compE2_stack_xliftD:
  "exec_meth ci P (compE2 e) (stack_xlift d (compxE2 e 0 0)) t h (stk, loc, pc, xcp) ta h' s'
  \<Longrightarrow> pc < length (compE2 e)"
by(cases s')(auto simp add: stack_xlift_compxE2)

lemma exec_meth_length_pc_xt_Nil:
  "exec_meth ci P ins [] t h (stk, loc, pc, xcp) ta h' s' \<Longrightarrow> pc < length ins"
apply(erule exec_meth.cases)
apply(auto dest: match_ex_table_pc_length_compE2)
done

lemma BinOp_exec2D:
  assumes exec: "exec_meth ci (compP2 P) (compE2 (e1 \<guillemotleft>bop\<guillemotright> e2)) (compxE2 (e1 \<guillemotleft>bop\<guillemotright> e2) 0 0) t h (stk @ [v1], loc, length (compE2 e1) + pc, xcp) ta h' (stk', loc', pc', xcp')"
  and pc: "pc < length (compE2 e2)"
  shows "exec_meth ci (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) t h (stk @ [v1], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e1), xcp') \<and> pc' \<ge> length (compE2 e1)"
proof
  from exec have "exec_meth ci (compP2 P) ((compE2 e1 @ compE2 e2) @ [BinOpInstr bop])
     (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) t h
     (stk @ [v1], loc, length (compE2 e1) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs compxE2_stack_xlift_convs)
  hence exec': "exec_meth ci (compP2 P) (compE2 e1 @ compE2 e2) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) t h
     (stk @ [v1], loc, length (compE2 e1) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take) (simp add: pc)
  thus "exec_meth ci (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) t h
     (stk @ [v1], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e1), xcp')"
    by(rule exec_meth_drop_xt) auto
  from exec' show "pc' \<ge> length (compE2 e1)"
   by(rule exec_meth_drop_xt_pc)(auto)
qed

lemma Call_execParamD:
  assumes exec: "exec_meth ci (compP2 P) (compE2 (obj\<bullet>M'(ps))) (compxE2 (obj\<bullet>M'(ps)) 0 0) t h (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')"
  and pc: "pc < length (compEs2 ps)"
  shows "exec_meth ci (compP2 P) (compEs2 ps) (stack_xlift (length [v]) (compxEs2 ps 0 0)) t h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 obj), xcp') \<and> pc' \<ge> length (compE2 obj)"
proof
  from exec have "exec_meth ci (compP2 P) ((compE2 obj @ compEs2 ps) @ [Invoke M' (length ps)])
     (compxE2 obj 0 0 @ shift (length (compE2 obj)) (stack_xlift (length [v]) (compxEs2 ps 0 0))) t h
     (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
  hence exec': "exec_meth ci (compP2 P) (compE2 obj @ compEs2 ps) (compxE2 obj 0 0 @ shift (length (compE2 obj)) (stack_xlift (length [v]) (compxEs2 ps 0 0))) t h
     (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(simp add: pc)
  thus "exec_meth ci (compP2 P) (compEs2 ps) (stack_xlift (length [v]) (compxEs2 ps 0 0)) t h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 obj), xcp')"
    by(rule exec_meth_drop_xt) auto
  from exec' show "pc' \<ge> length (compE2 obj)"
   by(rule exec_meth_drop_xt_pc)(auto)
qed

lemma exec_move_length_compE2D [dest]:
  "exec_move ci P t e h (stk, loc, pc, xcp) ta h' s' \<Longrightarrow> pc < length (compE2 e)"
by(cases s')(auto simp add: exec_move_def)

lemma exec_moves_length_compEs2D [dest]:
  "exec_moves ci P t es h (stk, loc, pc, xcp) ta h' s' \<Longrightarrow> pc < length (compEs2 es)"
by(cases s')(auto simp add: exec_moves_def)

lemma exec_meth_ci_appD:
  "\<lbrakk> exec_meth ci P ins xt t h (stk, loc, pc, None) ta h' fr' \<rbrakk>
  \<Longrightarrow>  ci_app ci (ins ! pc) P h stk loc undefined undefined pc []"
by(cases fr')(simp add: exec_meth_instr)

lemma exec_move_ci_appD:
  "exec_move ci P t E h (stk, loc, pc, None) ta h' fr'
  \<Longrightarrow> ci_app ci (compE2 E ! pc) (compP2 P) h stk loc undefined undefined pc []"
unfolding exec_move_def by(rule exec_meth_ci_appD)

lemma exec_moves_ci_appD:
  "exec_moves ci P t Es h (stk, loc, pc, None) ta h' fr'
  \<Longrightarrow> ci_app ci (compEs2 Es ! pc) (compP2 P) h stk loc undefined undefined pc []"
unfolding exec_moves_def by(rule exec_meth_ci_appD)

lemma \<tau>instr_stk_append_check:
  "check_instr' i P h stk loc C M pc frs \<Longrightarrow> \<tau>instr P h (stk @ vs) i = \<tau>instr P h stk i"
by(cases i)(simp_all add: nth_append)

lemma \<tau>instr_stk_drop_exec_move:
  "exec_move ci P t e h (stk, loc, pc, None) ta h' fr'
  \<Longrightarrow> \<tau>instr (compP2 P) h (stk @ vs) (compE2 e ! pc) = \<tau>instr (compP2 P) h stk (compE2 e ! pc)"
apply(drule exec_move_ci_appD)
apply(drule wf_ciD2_ci_app)
apply(erule \<tau>instr_stk_append_check)
done

lemma \<tau>instr_stk_drop_exec_moves:
  "exec_moves ci P t es h (stk, loc, pc, None) ta h' fr'
  \<Longrightarrow> \<tau>instr (compP2 P) h (stk @ vs) (compEs2 es ! pc) = \<tau>instr (compP2 P) h stk (compEs2 es ! pc)"
apply(drule exec_moves_ci_appD)
apply(drule wf_ciD2_ci_app)
apply(erule \<tau>instr_stk_append_check)
done

end

end
