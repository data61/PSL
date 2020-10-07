(*  Title:      JinjaThreads/MM/DRF_JVM.thy
    Author:     Andreas Lochbihler
*)

section \<open>JMM Instantiation for bytecode\<close>

theory DRF_JVM
imports
  JMM_Common
  JMM_JVM
  "../BV/BVProgressThreaded"
  SC_Legal
begin

subsection \<open>DRF guarantee for the JVM\<close>

abbreviation (input) ka_xcp :: "'addr option \<Rightarrow> 'addr set"
where "ka_xcp \<equiv> set_option"

primrec jvm_ka :: "'addr jvm_thread_state \<Rightarrow> 'addr set"
where
  "jvm_ka (xcp, frs) = 
   ka_xcp xcp \<union> (\<Union>(stk, loc, C, M, pc) \<in> set frs. (\<Union>v \<in> set stk. ka_Val v) \<union> (\<Union>v \<in> set loc. ka_Val v))"

context heap begin

lemma red_external_aggr_read_mem_typeable:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>T'. P,h \<turnstile> ad@al : T'"
by(auto simp add: red_external_aggr_def split_beta split: if_split_asm dest: heap_clone_read_typeable)

end

context JVM_heap_base begin

definition jvm_known_addrs :: "'thread_id \<Rightarrow> 'addr jvm_thread_state \<Rightarrow> 'addr set"
where "jvm_known_addrs t xcpfrs = {thread_id2addr t} \<union> jvm_ka xcpfrs \<union> set start_addrs"

end

context JVM_heap begin

lemma exec_instr_known_addrs:
  assumes ok: "start_heap_ok"
  and exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  shows "jvm_known_addrs t (xcp', frs') \<subseteq> jvm_known_addrs t (None, (stk, loc, C, M, pc) # frs) \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
proof -
  
  note [simp] = jvm_known_addrs_def new_obs_addrs_def addr_of_sys_xcpt_start_addr[OF ok] subset_Un1 subset_Un2 subset_insert ka_Val_subset_new_obs_Addr_ReadMem SUP_subset_mono split_beta neq_Nil_conv tl_conv_drop set_drop_subset is_Ref_def

  from exec check show ?thesis
  proof(cases "i")
    case Load with exec check show ?thesis by auto
  next
    case (Store V) with exec check show ?thesis
      using set_update_subset_insert[of loc V]
      by(clarsimp simp del: set_update_subsetI) blast
  next
    case (Push v)
    with check have "ka_Val v = {}" by(cases v) simp_all
    with Push exec check show ?thesis by(simp)
  next
    case (CAS F D)
    then show ?thesis using exec check 
      by(clarsimp split: if_split_asm)(fastforce dest!: in_set_dropD)+
  next
    case (Invoke M' n)
    show ?thesis
    proof(cases "stk ! n = Null")
      case True with exec check Invoke show ?thesis by(simp)
    next
      case [simp]: False
      with check Invoke obtain a where stkn: "stk ! n = Addr a" "n < length stk" by auto
      hence a: "a \<in> (\<Union>v \<in> set stk. ka_Val v)" by(fastforce dest: nth_mem)
      show ?thesis
      proof(cases "snd (snd (snd (method P (class_type_of (the (typeof_addr h (the_Addr (stk ! n))))) M'))) = Native")
        case True
        with exec check Invoke a stkn show ?thesis
          apply clarsimp
          apply(drule red_external_aggr_known_addrs_mono[OF ok], simp)
          apply(auto dest!: in_set_takeD dest: bspec subsetD split: extCallRet.split_asm simp add: has_method_def is_native.simps)
          done
      next
        case False
        with exec check Invoke a stkn show ?thesis
          by(auto simp add: set_replicate_conv_if dest!: in_set_takeD)
      qed
    qed
  next
    case Swap with exec check show ?thesis
      by(cases stk)(simp, case_tac list, auto)
  next
    case (BinOpInstr bop) with exec check show ?thesis
      using binop_known_addrs[OF ok, of bop "hd (drop (Suc 0) stk)" "hd stk"]
      apply(cases stk)
      apply(simp, case_tac list, simp)
      apply clarsimp
      apply(drule (2) binop_progress)
      apply(auto 6 2 split: sum.split_asm)
      done
  next
    case MExit with exec check show ?thesis by(auto split: if_split_asm)
  qed(clarsimp split: if_split_asm)+
qed

lemma exec_d_known_addrs_mono:
  assumes ok: "start_heap_ok"
  and exec: "mexecd P t (xcpfrs, h) ta (xcpfrs', h')"
  shows "jvm_known_addrs t xcpfrs' \<subseteq> jvm_known_addrs t xcpfrs \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using exec
apply(cases xcpfrs)
apply(cases xcpfrs')
apply(simp add: split_beta)
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
 apply(fastforce simp add: check_def split_beta del: subsetI dest!: exec_instr_known_addrs[OF ok])
apply(fastforce simp add: jvm_known_addrs_def split_beta dest!: in_set_dropD)
done

lemma exec_instr_known_addrs_ReadMem:
  assumes exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  and read: "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "ad \<in> jvm_known_addrs t (None, (stk, loc, C, M, pc) # frs)"
using assms
proof(cases i)
  case ALoad thus ?thesis using assms
    by(cases stk)(case_tac [2] list, auto simp add: split_beta is_Ref_def jvm_known_addrs_def split: if_split_asm)
next
  case (Invoke M n)
  with check have "stk ! n \<noteq> Null \<longrightarrow> the_Addr (stk ! n) \<in> ka_Val (stk ! n)" "stk ! n \<in> set stk"
    by(auto simp add: is_Ref_def)
  with assms Invoke show ?thesis
    by(auto simp add: split_beta is_Ref_def simp del: ka_Val.simps nth_mem split: if_split_asm dest!: red_external_aggr_known_addrs_ReadMem in_set_takeD del: is_AddrE)(auto simp add: jvm_known_addrs_def simp del: ka_Val.simps nth_mem del: is_AddrE)
next
  case Getfield thus ?thesis using assms
    by(auto simp add: jvm_known_addrs_def neq_Nil_conv is_Ref_def split: if_split_asm)
next
  case CAS thus ?thesis using assms
    apply(cases stk; simp)
    subgoal for v stk
      apply(cases stk; simp)
      subgoal for v stk
        by(cases stk)(auto split: if_split_asm simp add: jvm_known_addrs_def is_Ref_def)
      done
    done
qed(auto simp add: split_beta is_Ref_def neq_Nil_conv split: if_split_asm)

lemma mexecd_known_addrs_ReadMem:
  "\<lbrakk> mexecd P t (xcpfrs, h) ta (xcpfrs', h'); ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> jvm_known_addrs t xcpfrs"
apply(cases xcpfrs)
apply(cases xcpfrs')
apply simp
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
apply(auto simp add: check_def dest: exec_instr_known_addrs_ReadMem)
done

lemma exec_instr_known_addrs_WriteMem:
  assumes exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  and "write": "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr a)" "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "a \<in> jvm_known_addrs t (None, (stk, loc, C, M, pc) # frs) \<or> a \<in> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
using assms
proof(cases i)
  case (Invoke M n)
  with check have "stk ! n \<noteq> Null \<longrightarrow> the_Addr (stk ! n) \<in> ka_Val (stk ! n)" "stk ! n \<in> set stk"
    by(auto simp add: is_Ref_def)
  thus ?thesis using assms Invoke
    by(auto simp add: is_Ref_def split_beta split: if_split_asm simp del: ka_Val.simps nth_mem dest!: red_external_aggr_known_addrs_WriteMem in_set_takeD del: is_AddrE)(auto simp add: jvm_known_addrs_def del: is_AddrE)
next
  case AStore with assms show ?thesis
    by(cases stk)(auto simp add: jvm_known_addrs_def split: if_split_asm)
next
  case Putfield with assms show ?thesis
    by(cases stk)(auto simp add: jvm_known_addrs_def split: if_split_asm)
next
  case CAS with assms show ?thesis
    apply(cases stk; simp)
    subgoal for v stk
      apply(cases stk; simp)
      subgoal for v stk
        by(cases stk)(auto split: if_split_asm simp add: take_Cons' jvm_known_addrs_def)
      done
    done
qed(auto simp add: split_beta split: if_split_asm)

lemma mexecd_known_addrs_WriteMem:
  "\<lbrakk> mexecd P t (xcpfrs, h) ta (xcpfrs', h'); \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr a); n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> a \<in> jvm_known_addrs t xcpfrs \<or> a \<in> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
apply(cases xcpfrs)
apply(cases xcpfrs')
apply simp
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
apply(auto simp add: check_def dest: exec_instr_known_addrs_WriteMem)
done

lemma exec_instr_known_addrs_new_thread:
  assumes exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  and new: "NewThread t' x' h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "jvm_known_addrs t' x' \<subseteq> jvm_known_addrs t (None, (stk, loc, C, M, pc) # frs)"
using assms
proof(cases i)
  case (Invoke M n)
  with assms have "stk ! n \<noteq> Null \<longrightarrow> the_Addr (stk ! n) \<in> ka_Val (stk ! n) \<and> thread_id2addr (addr2thread_id (the_Addr (stk ! n))) = the_Addr (stk ! n)" "stk ! n \<in> set stk"
    apply(auto simp add: is_Ref_def split: if_split_asm)
    apply(frule red_external_aggr_NewThread_idD, simp, simp)
    apply(drule red_external_aggr_new_thread_sub_thread)
    apply(auto intro: addr2thread_id_inverse)
    done
  with assms Invoke show ?thesis
    apply(auto simp add: is_Ref_def split_beta split: if_split_asm simp del: nth_mem del: is_AddrE)
    apply(drule red_external_aggr_NewThread_idD)
    apply(auto simp add: extNTA2JVM_def jvm_known_addrs_def split_beta simp del: nth_mem del: is_AddrE)
    done
qed(auto simp add: split_beta split: if_split_asm)

lemma mexecd_known_addrs_new_thread:
  "\<lbrakk> mexecd P t (xcpfrs, h) ta (xcpfrs', h'); NewThread t' x' h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> jvm_known_addrs t' x' \<subseteq> jvm_known_addrs t xcpfrs"
apply(cases xcpfrs)
apply(cases xcpfrs')
apply simp
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
apply(auto 4 3 simp add: check_def dest: exec_instr_known_addrs_new_thread)
done

lemma exec_instr_New_same_addr_same:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr ins P t h stk loc C M pc frs;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
apply(cases ins)
apply(auto simp add: nth_Cons' split: prod.split_asm if_split_asm)
apply(auto split: extCallRet.split_asm dest: red_external_aggr_New_same_addr_same)
done

lemma exec_New_same_addr_same:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec P t (xcp, h, frs); 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
apply(cases "(P, t, xcp, h, frs)" rule: exec.cases)
apply(auto dest: exec_instr_New_same_addr_same)
done

lemma exec_1_d_New_same_addr_same:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
by(erule jvmd_NormalE)(rule exec_New_same_addr_same)

end



locale JVM_allocated_heap = allocated_heap +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and P :: "'addr jvm_prog"

sublocale JVM_allocated_heap < JVM_heap
by(unfold_locales)

context JVM_allocated_heap begin

lemma exec_instr_allocated_mono:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs; check_instr i P h stk loc C M pc frs \<rbrakk>
  \<Longrightarrow> allocated h \<subseteq> allocated h'"
apply(cases i)
apply(auto 4 4 simp add: split_beta has_method_def is_native.simps split: if_split_asm sum.split_asm intro: allocate_allocated_mono dest: heap_write_allocated_same dest!: red_external_aggr_allocated_mono del: subsetI)
done

lemma mexecd_allocated_mono:
  "mexecd P t (xcpfrs, h) ta (xcpfrs', h') \<Longrightarrow> allocated h \<subseteq> allocated h'"
apply(cases xcpfrs)
apply(cases xcpfrs')
apply(simp)
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
apply(auto del: subsetI simp add: check_def dest: exec_instr_allocated_mono)
done

lemma exec_instr_allocatedD:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs; 
     check_instr i P h stk loc C M pc frs; NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> allocated h' \<and> ad \<notin> allocated h"
apply(cases i)
apply(auto 4 4 split: if_split_asm prod.split_asm dest: allocate_allocatedD dest!: red_external_aggr_allocatedD simp add: has_method_def is_native.simps)
done

lemma mexecd_allocatedD:
  "\<lbrakk> mexecd P t (xcpfrs, h) ta (xcpfrs', h'); NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> ad \<in> allocated h' \<and> ad \<notin> allocated h"
apply(cases xcpfrs)
apply(cases xcpfrs')
apply(simp)
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
apply(auto del: subsetI dest: exec_instr_allocatedD simp add: check_def)
done

lemma exec_instr_NewHeapElemD:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs; check_instr i P h stk loc C M pc frs;
     ad \<in> allocated h'; ad \<notin> allocated h \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
apply(cases i)
apply(auto 4 3 split: if_split_asm prod.split_asm sum.split_asm dest: allocate_allocatedD heap_write_allocated_same dest!: red_external_aggr_NewHeapElemD simp add: is_native.simps has_method_def)
done

lemma mexecd_NewHeapElemD:
  "\<lbrakk> mexecd P t (xcpfrs, h) ta (xcpfrs', h'); ad \<in> allocated h'; ad \<notin> allocated h \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
apply(cases xcpfrs)
apply(cases xcpfrs')
apply(simp)
apply(erule jvmd_NormalE)
apply(cases "fst xcpfrs")
apply(auto dest: exec_instr_NewHeapElemD simp add: check_def)
done

lemma mexecd_allocated_multithreaded:
  "allocated_multithreaded addr2thread_id thread_id2addr empty_heap allocate typeof_addr heap_write allocated JVM_final (mexecd P) P"
proof
  fix t x m ta x' m'
  assume "mexecd P t (x, m) ta (x', m')"
  thus "allocated m \<subseteq> allocated m'" by(rule mexecd_allocated_mono)
next
  fix x t m ta x' m' ad CTn
  assume "mexecd P t (x, m) ta (x', m')"
    and "NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "ad \<in> allocated m' \<and> ad \<notin> allocated m" by(rule mexecd_allocatedD)
next
  fix t x m ta x' m' ad
  assume "mexecd P t (x, m) ta (x', m')"
    and "ad \<in> allocated m'" "ad \<notin> allocated m"
  thus "\<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by(rule mexecd_NewHeapElemD)
next
  fix t x m ta x' m' i a CTn j CTn'
  assume "mexecd P t (x, m) ta (x', m')"
    and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a CTn" "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a CTn'" "j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "i = j" by(auto dest: exec_1_d_New_same_addr_same simp add: split_beta)
qed

end

sublocale JVM_allocated_heap < execd_mthr: allocated_multithreaded 
  addr2thread_id thread_id2addr 
  spurious_wakeups
  empty_heap allocate typeof_addr heap_read heap_write allocated 
  JVM_final "mexecd P" 
  P
by(rule mexecd_allocated_multithreaded)

context JVM_allocated_heap begin

lemma mexecd_known_addrs: 
  assumes wf: "wf_prog wfmd P"
  and ok: "start_heap_ok"
  shows "known_addrs addr2thread_id thread_id2addr empty_heap allocate typeof_addr heap_write allocated jvm_known_addrs JVM_final (mexecd P) P"
proof
  fix t x m ta x' m'
  assume "mexecd P t (x, m) ta (x', m')"
  thus "jvm_known_addrs t x' \<subseteq> jvm_known_addrs t x \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    by(rule exec_d_known_addrs_mono[OF ok])
next
  fix t x m ta x' m' t' x'' m''
  assume "mexecd P t (x, m) ta (x', m')"
    and "NewThread t' x'' m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  thus "jvm_known_addrs t' x'' \<subseteq> jvm_known_addrs t x" by(rule mexecd_known_addrs_new_thread)
next
  fix t x m ta x' m' ad al v
  assume "mexecd P t (x, m) ta (x', m')"
    and "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "ad \<in> jvm_known_addrs t x" by(rule mexecd_known_addrs_ReadMem)
next
  fix t x m ta x' m' n ad al ad'
  assume "mexecd P t (x, m) ta (x', m')"
    and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr ad')" "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "ad' \<in> jvm_known_addrs t x \<or> ad' \<in> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
    by(rule mexecd_known_addrs_WriteMem)
qed

end

context JVM_heap begin

lemma exec_instr_read_typeable:
  assumes exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  and read: "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "\<exists>T'. P,h \<turnstile> ad@al : T'"
using exec check read
proof(cases i)
  case ALoad
  with assms show ?thesis
    by(fastforce simp add: split_beta is_Ref_def nat_less_iff word_sless_alt intro: addr_loc_type.intros split: if_split_asm)
next
  case (Getfield F D)
  with assms show ?thesis
    by(clarsimp simp add: split_beta is_Ref_def split: if_split_asm)(blast intro: addr_loc_type.intros dest: has_visible_field has_field_mono)
next
  case (Invoke M n)
  with exec check read obtain a vs ta' va T
    where "(ta', va, h') \<in> red_external_aggr P t a M vs h"
    and "ReadMem ad al v \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
    by(auto split: if_split_asm simp add: is_Ref_def)
  thus ?thesis by(rule red_external_aggr_read_mem_typeable)
next
  case (CAS F D)
  with assms show ?thesis
    by(clarsimp simp add: split_beta is_Ref_def conf_def split: if_split_asm)
      (force intro: addr_loc_type.intros dest: has_visible_field[THEN has_field_mono])
qed(auto simp add: split_beta is_Ref_def split: if_split_asm)

lemma exec_1_d_read_typeable:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); 
     ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>T'. P,h \<turnstile> ad@al : T'"
apply(erule jvmd_NormalE)
apply(cases "(P, t, xcp, h, frs)" rule: exec.cases)
apply(auto intro: exec_instr_read_typeable simp add: check_def)
done

end

sublocale JVM_heap_base < execd_mthr: 
  if_multithreaded
    JVM_final
    "mexecd P"
    convert_RA
  for P
by(unfold_locales)

context JVM_heap_conf begin

lemma JVM_conf_read_heap_read_typed:
  "JVM_conf_read addr2thread_id thread_id2addr empty_heap allocate typeof_addr (heap_read_typed P) heap_write hconf P"
proof -
  interpret conf: heap_conf_read
    addr2thread_id thread_id2addr 
    spurious_wakeups
    empty_heap allocate typeof_addr "heap_read_typed P" heap_write hconf 
    P
    by(rule heap_conf_read_heap_read_typed)
  show ?thesis by(unfold_locales)
qed

lemma exec_instr_New_typeof_addrD:
  "\<lbrakk> (ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs; 
     check_instr i P h stk loc C M pc frs; hconf h;
     NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr h' a = Some x"
apply(cases i)
apply(auto dest: allocate_SomeD split: prod.split_asm if_split_asm)
apply(auto 4 4 split: extCallRet.split_asm dest!: red_external_aggr_New_typeof_addrD simp add: has_method_def is_native.simps)
done

lemma exec_1_d_New_typeof_addrD:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; hconf h \<rbrakk>
  \<Longrightarrow> typeof_addr h' a = Some x"
apply(erule jvmd_NormalE)
apply(cases "xcp")
apply(auto dest: exec_instr_New_typeof_addrD simp add: check_def)
done

lemma exec_instr_non_speculative_typeable:
  assumes exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  and sc: "non_speculative P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
  and vs_conf: "vs_conf P h vs"
  and hconf: "hconf h"
  shows "(ta, xcp', h', frs') \<in> JVM_heap_base.exec_instr addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_read_typed P) heap_write i P t h stk loc C M pc frs"
proof -
  note [simp] = JVM_heap_base.exec_instr.simps
    and [split] = if_split_asm prod.split_asm sum.split_asm
    and [split del] = if_split
  from assms show "?thesis"
  proof(cases i)
    case ALoad with assms show ?thesis
      by(auto 4 3 intro!: heap_read_typedI dest: vs_confD addr_loc_type_fun)
  next
    case Getfield with assms show ?thesis
      by(auto 4 3 intro!: heap_read_typedI dest: vs_confD addr_loc_type_fun)
  next
    case CAS with assms show ?thesis
      by(auto 4 3 intro!: heap_read_typedI dest: vs_confD addr_loc_type_fun)
  next
    case Invoke with assms show ?thesis
      by(fastforce dest: red_external_aggr_non_speculative_typeable simp add: has_method_def is_native.simps)
  qed(auto)
qed

lemma exec_instr_non_speculative_vs_conf:
  assumes exec: "(ta, xcp', h', frs') \<in> exec_instr i P t h stk loc C M pc frs"
  and check: "check_instr i P h stk loc C M pc frs"
  and sc: "non_speculative P vs (llist_of (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
  and vs_conf: "vs_conf P h vs"
  and hconf: "hconf h"
  shows "vs_conf P h' (w_values P vs (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
proof -
  note [simp] = JVM_heap_base.exec_instr.simps take_Cons'
    and [split] = if_split_asm prod.split_asm sum.split_asm
    and [split del] = if_split
  from assms show ?thesis
  proof(cases i)
    case New with assms show ?thesis
      by(auto 4 4 dest: hext_allocate vs_conf_allocate intro: vs_conf_hext)
  next
    case NewArray with assms show ?thesis
      by(auto 4 4 dest: hext_allocate vs_conf_allocate intro: vs_conf_hext cong: if_cong)
  next
    case Invoke with assms show ?thesis
      by(fastforce dest: red_external_aggr_non_speculative_vs_conf simp add: has_method_def is_native.simps)
  next
    case AStore
    { 
      assume "hd (tl (tl stk)) \<noteq> Null"
        and "\<not> the_Intg (hd (tl stk))  <s 0"
        and "\<not> int (alen_of_htype (the (typeof_addr h (the_Addr (hd (tl (tl stk))))))) \<le> sint (the_Intg (hd (tl stk)))"
        and "P \<turnstile> the (typeof\<^bsub>h\<^esub> (hd stk)) \<le> the_Array (ty_of_htype (the (typeof_addr h (the_Addr (hd (tl (tl stk)))))))"
      moreover hence "nat (sint (the_Intg (hd (tl stk)))) < alen_of_htype (the (typeof_addr h (the_Addr (hd (tl (tl stk))))))"
        by(auto simp add: not_le nat_less_iff word_sle_def word_sless_def not_less)
      with assms AStore have "nat (sint (the_Intg (hd (tl stk)))) < alen_of_htype (the (typeof_addr h' (the_Addr (hd (tl (tl stk))))))"
        by(auto dest!: hext_arrD hext_heap_write)
      ultimately have "\<exists>T. P,h' \<turnstile> the_Addr (hd (tl (tl stk)))@ACell (nat (sint (the_Intg (hd (tl stk))))) : T \<and> P,h' \<turnstile> hd stk :\<le> T"
        using assms AStore
        by(auto 4 4 simp add: is_Ref_def conf_def dest!: hext_heap_write dest: hext_arrD intro!: addr_loc_type.intros intro: typeof_addr_hext_mono type_of_hext_type_of) }
    thus ?thesis using assms AStore
      by(auto intro!: vs_confI)(blast intro: addr_loc_type_hext_mono conf_hext dest: hext_heap_write vs_confD)+
  next
    case Putfield
    show ?thesis using assms Putfield
      by(auto intro!: vs_confI dest!: hext_heap_write)(blast intro: addr_loc_type.intros addr_loc_type_hext_mono typeof_addr_hext_mono has_field_mono[OF has_visible_field] conf_hext dest: vs_confD)+
  next
    case CAS
    show ?thesis using assms CAS
      by(auto intro!: vs_confI dest!: hext_heap_write)(blast intro: addr_loc_type.intros addr_loc_type_hext_mono typeof_addr_hext_mono has_field_mono[OF has_visible_field] conf_hext dest: vs_confD)+
  qed(auto)
qed

lemma mexecd_non_speculative_typeable:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, stk) -ta-jvmd\<rightarrow> Normal (xcp', h', frs'); non_speculative P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>));
    vs_conf P h vs; hconf h \<rbrakk>
  \<Longrightarrow> JVM_heap_base.exec_1_d addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_read_typed P) heap_write P t (Normal (xcp, h, stk)) ta (Normal (xcp', h', frs'))"
apply(erule jvmd_NormalE)
apply(cases xcp)
apply(auto intro!: JVM_heap_base.exec_1_d.intros simp add: JVM_heap_base.exec_d_def check_def JVM_heap_base.exec.simps intro: exec_instr_non_speculative_typeable)
done

lemma mexecd_non_speculative_vs_conf:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, stk) -ta-jvmd\<rightarrow> Normal (xcp', h', frs');
    non_speculative P vs (llist_of (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)));
    vs_conf P h vs; hconf h \<rbrakk>
  \<Longrightarrow> vs_conf P h' (w_values P vs (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
apply(erule jvmd_NormalE)
apply(cases xcp)
apply(auto intro!: JVM_heap_base.exec_1_d.intros simp add: JVM_heap_base.exec_d_def check_def JVM_heap_base.exec.simps intro: exec_instr_non_speculative_vs_conf)
done

end

locale JVM_allocated_heap_conf = 
  JVM_heap_conf 
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write hconf
    P
  +
  JVM_allocated_heap 
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    allocated
    P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and P :: "'addr jvm_prog"
begin

lemma mexecd_known_addrs_typing:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and ok: "start_heap_ok"
  shows "known_addrs_typing addr2thread_id thread_id2addr empty_heap allocate typeof_addr heap_write allocated jvm_known_addrs JVM_final (mexecd P) (\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>) P"
proof -
  from wf obtain wf_md where "wf_prog wf_md P" by(blast dest: wt_jvm_progD)
  then
  interpret known_addrs
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    allocated jvm_known_addrs
    JVM_final "mexecd P" P
    using ok by(rule mexecd_known_addrs)
  
  show ?thesis
  proof
    fix t x m ta x' m'
    assume "mexecd P t (x, m) ta (x', m')"
    thus "m \<unlhd> m'" by(auto simp add: split_beta intro: exec_1_d_hext)
  next
    fix t x m ta x' m' vs
    assume exec: "mexecd P t (x, m) ta (x', m')"
      and ts_ok: "(\<lambda>(xcp, frstls) h. \<Phi> \<turnstile> t:(xcp, h, frstls) \<surd>) x m"
      and vs: "vs_conf P m vs"
      and ns: "non_speculative P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"

    let ?mexecd = "JVM_heap_base.mexecd addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_read_typed P) heap_write P"    
    have lift: "lifting_wf JVM_final ?mexecd (\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>)"
      by(intro JVM_conf_read.lifting_wf_correct_state_d JVM_conf_read_heap_read_typed wf)

    from exec ns vs ts_ok have exec': "?mexecd t (x, m) ta (x', m')"
      by(auto simp add: split_beta correct_state_def dest: mexecd_non_speculative_typeable)
    thus "(\<lambda>(xcp, frstls) h. \<Phi> \<turnstile> t:(xcp, h, frstls) \<surd>) x' m'" using ts_ok
      by(rule lifting_wf.preserves_red[OF lift])
    {
      fix t'' x'' m''
      assume New: "NewThread t'' x'' m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
      with exec have "m'' = snd (x', m')" by(rule execd_mthr.new_thread_memory)
      thus "(\<lambda>(xcp, frstls) h. \<Phi> \<turnstile> t'':(xcp, h, frstls) \<surd>) x'' m''"
        using lifting_wf.preserves_NewThread[where ?r="?mexecd", OF lift exec' ts_ok] New
        by auto }
    { fix t'' x''
      assume "(\<lambda>(xcp, frstls) h. \<Phi> \<turnstile> t'':(xcp, h, frstls) \<surd>) x'' m"
      with lift exec' ts_ok show "(\<lambda>(xcp, frstls) h. \<Phi> \<turnstile> t'':(xcp, h, frstls) \<surd>) x'' m'"
        by(rule lifting_wf.preserves_other) }
  next
    fix t x m ta x' m' vs n
    assume exec: "mexecd P t (x, m) ta (x', m')"
      and ts_ok: "(\<lambda>(xcp, frstls) h. \<Phi> \<turnstile> t:(xcp, h, frstls) \<surd>) x m"
      and vs: "vs_conf P m vs"
      and ns: "non_speculative P vs (llist_of (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
    thus "vs_conf P m' (w_values P vs (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
      by(auto simp add: correct_state_def dest: mexecd_non_speculative_vs_conf)
  next
    fix t x m ta x' m' ad al v
    assume "mexecd P t (x, m) ta (x', m')"
      and "(\<lambda>(xcp, frstls) h. \<Phi> \<turnstile> t:(xcp, h, frstls) \<surd>) x m"
      and "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    thus "\<exists>T. P,m \<turnstile> ad@al : T"
      by(auto simp add: correct_state_def split_beta dest: exec_1_d_read_typeable)
  next
    fix t x m ta x' m' ad hT
    assume "mexecd P t (x, m) ta (x', m')"
      and "(\<lambda>(xcp, frstls) h. \<Phi> \<turnstile> t:(xcp, h, frstls) \<surd>) x m"
      and "NewHeapElem ad hT \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    thus "typeof_addr m' ad = \<lfloor>hT\<rfloor>"
      by(auto dest: exec_1_d_New_typeof_addrD[where x="hT"] simp add: split_beta correct_state_def)
  qed
qed

lemma executions_sc:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and wf_start: "wf_start_state P C M vs"
  and vs2: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "executions_sc_hb (JVMd_\<E> P C M vs status) P"
    (is "executions_sc_hb ?E P")
proof -
  from wf_start obtain Ts T meth D where ok: "start_heap_ok"
    and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>meth\<rfloor> in D"
    and vs1: "P,start_heap \<turnstile> vs [:\<le>] Ts" by cases

  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    allocated jvm_known_addrs
    JVM_final "mexecd P" "\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>" P
    using wf ok by(rule mexecd_known_addrs_typing)
  
  from wf obtain wf_md where wf': "wf_prog wf_md P" by(blast dest: wt_jvm_progD)
  hence "wf_syscls P" by(rule wf_prog_wf_syscls) 
  thus ?thesis
  proof(rule executions_sc_hb)
    from correct_jvm_state_initial[OF wf wf_start]
    show "correct_state_ts \<Phi> (thr (JVM_start_state P C M vs)) start_heap"
      by(simp add: correct_jvm_state_def start_state_def split_beta)
  next
    show "jvm_known_addrs start_tid ((\<lambda>(mxs, mxl0, b) vs. (None, [([], Null # vs @ replicate mxl0 undefined_value, fst (method P C M), M, 0)])) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
      using vs2
      by(auto simp add: split_beta start_addrs_allocated jvm_known_addrs_def intro: start_tid_start_addrs[OF \<open>wf_syscls P\<close> ok])
  qed
qed

end

declare split_paired_Ex [simp del]
declare eq_upto_seq_inconsist_simps [simp]

context JVM_progress begin

abbreviation (input) jvm_non_speculative_read_bound :: nat where
  "jvm_non_speculative_read_bound \<equiv> 2"

lemma exec_instr_non_speculative_read:
  assumes hrt: "heap_read_typeable hconf P"
  and vs: "vs_conf P (shr s) vs"
  and hconf: "hconf (shr s)"
  and exec_i: "(ta, xcp', h', frs') \<in> exec_instr i P t (shr s) stk loc C M pc frs"
  and check: "check_instr i P (shr s) stk loc C M pc frs"
  and aok: "execd_mthr.mthr.if.actions_ok s t ta"
  and i: "I < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and read: "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! I = ReadMem a'' al'' v"
  and v': "v' \<in> w_values P vs (map NormalAction (take I \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (a'', al'')"
  and ns: "non_speculative P vs (llist_of (map NormalAction (take I \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
  shows "\<exists>ta' xcp'' h'' frs''. (ta', xcp'', h'', frs'') \<in> exec_instr i P t (shr s) stk loc C M pc frs \<and>
           execd_mthr.mthr.if.actions_ok s t ta' \<and> 
           I < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<and> take I \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take I \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> 
           \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! I = ReadMem a'' al'' v' \<and> 
           length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> max jvm_non_speculative_read_bound (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
using exec_i i read
proof(cases i)
  case [simp]: ALoad
  let ?a = "the_Addr (hd (tl stk))"
  let ?i = "the_Intg (hd stk)"
  from exec_i i read have Null: "hd (tl stk) \<noteq> Null"
    and bounds: "0 <=s ?i" "sint ?i < int (alen_of_htype (the (typeof_addr (shr s) ?a)))"
    and [simp]: "I = 0" "a'' = ?a" "al'' = ACell (nat (sint ?i))"
    by(auto split: if_split_asm)

  from Null check obtain a T n 
    where a: "length stk > 1" "hd (tl stk) = Addr a"
    and type: "typeof_addr (shr s) ?a = \<lfloor>Array_type T n\<rfloor>" by(fastforce simp add: is_Ref_def)
  from bounds type have "nat (sint ?i) < n"
    by(simp add: word_sle_def nat_less_iff)
  with type have adal: "P,shr s \<turnstile> ?a@ACell (nat (sint ?i)) : T"
    by(rule addr_loc_type.intros)
  from v' vs adal have "P,shr s \<turnstile> v' :\<le> T" by(auto dest!: vs_confD dest: addr_loc_type_fun)
  with hrt adal have "heap_read (shr s) ?a (ACell (nat (sint ?i))) v'" using hconf by(rule heap_read_typeableD)
  with type bounds Null aok exec_i show ?thesis by(fastforce)
next
  case [simp]: (Getfield F D)
  let ?a = "the_Addr (hd stk)"

  from exec_i i read have Null: "hd stk \<noteq> Null"
    and [simp]: "I = 0" "a'' = ?a" "al'' = CField D F"
    by(auto split: if_split_asm)
  with check obtain U T fm C' a
    where sees: "P \<turnstile> D sees F:T (fm) in D"
    and type: "typeof_addr (shr s) ?a = \<lfloor>U\<rfloor>" 
    and sub: "P \<turnstile> class_type_of U \<preceq>\<^sup>* D" 
    and a: "hd stk = Addr a" "length stk > 0" by(auto simp add: is_Ref_def)
  from has_visible_field[OF sees] sub
  have "P \<turnstile> class_type_of U has F:T (fm) in D" by(rule has_field_mono)
  with type have adal: "P,shr s \<turnstile> ?a@CField D F : T"
    by(rule addr_loc_type.intros)
  from v' vs adal have "P,shr s \<turnstile> v' :\<le> T" by(auto dest!: vs_confD dest: addr_loc_type_fun)  
  with hrt adal have "heap_read (shr s) ?a (CField D F) v'" using hconf by(rule heap_read_typeableD)
  with type Null aok exec_i show ?thesis by(fastforce)
next
  case [simp]: (CAS F D)
  let ?a = "the_Addr (hd (tl (tl stk)))"

  from exec_i i read have Null: "hd (tl (tl stk)) \<noteq> Null"
    and [simp]: "I = 0" "a'' = ?a" "al'' = CField D F"
    by(auto split: if_split_asm simp add: nth_Cons')
  with check obtain U T fm C' a
    where sees: "P \<turnstile> D sees F:T (fm) in D"
    and type: "typeof_addr (shr s) ?a = \<lfloor>U\<rfloor>" 
    and sub: "P \<turnstile> class_type_of U \<preceq>\<^sup>* D" 
    and a: "hd (tl (tl stk)) = Addr a" "length stk > 2" 
    and v: "P,shr s \<turnstile> hd stk :\<le> T"
    by(auto simp add: is_Ref_def)
  from has_visible_field[OF sees] sub
  have "P \<turnstile> class_type_of U has F:T (fm) in D" by(rule has_field_mono)
  with type have adal: "P,shr s \<turnstile> ?a@CField D F : T"
    by(rule addr_loc_type.intros)
  from v' vs adal have "P,shr s \<turnstile> v' :\<le> T" by(auto dest!: vs_confD dest: addr_loc_type_fun)  
  with hrt adal have read: "heap_read (shr s) ?a (CField D F) v'" using hconf by(rule heap_read_typeableD)
  show ?thesis
  proof(cases "v' = hd (tl stk)")
    case True
    from heap_write_total[OF hconf adal v] a obtain h'
      where "heap_write (shr s) a (CField D F) (hd stk) h'" by auto
    then show ?thesis using read a True aok exec_i by fastforce
  next
    case False
    then show ?thesis using read a aok exec_i
      by(fastforce intro!: disjI2)
  qed
next
  case [simp]: (Invoke M n)
  let ?a = "the_Addr (stk ! n)"
  let ?vs = "rev (take n stk)"
  from exec_i i read have Null: "stk ! n \<noteq> Null" 
    and iec: "snd (snd (snd (method P (class_type_of (the (typeof_addr (shr s) ?a))) M))) = Native"
    by(auto split: if_split_asm)
  with check obtain a T Ts Tr D
    where a: "stk ! n = Addr a" "n < length stk"
    and type: "typeof_addr (shr s) ?a = \<lfloor>T\<rfloor>"
    and extwt: "P \<turnstile> class_type_of T sees M:Ts\<rightarrow>Tr = Native in D" "D\<bullet>M(Ts) :: Tr"
    by(auto simp add: is_Ref_def has_method_def)
  from extwt have native: "is_native P T M" by(auto simp add: is_native.simps)
  from Null iec type exec_i obtain ta' va
    where red: "(ta', va, h') \<in> red_external_aggr P t ?a M ?vs (shr s)"
    and ta: "ta = extTA2JVM P ta'" by(fastforce)
  from aok ta have aok': "execd_mthr.mthr.if.actions_ok s t ta'" by simp
  from red_external_aggr_non_speculative_read[OF hrt vs red[unfolded a the_Addr.simps] _ aok' hconf, of I a'' al'' v v']
    native type i read v' ns a ta
  obtain ta'' va'' h''
    where "(ta'', va'', h'') \<in> red_external_aggr P t a M (rev (take n stk)) (shr s)"
    and "execd_mthr.mthr.if.actions_ok s t ta''"
    and "I < length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>" "take I \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> = take I \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" 
    and "\<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> ! I = ReadMem a'' al'' v'" "length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> \<le> length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" by auto
  thus ?thesis using Null iec ta extwt a type
    by(cases va'') force+
qed(auto simp add: split_beta split: if_split_asm)

lemma exec_1_d_non_speculative_read:
  assumes hrt: "heap_read_typeable hconf P"
  and vs: "vs_conf P (shr s) vs"
  and exec: "P,t \<turnstile> Normal (xcp, shr s, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
  and aok: "execd_mthr.mthr.if.actions_ok s t ta"
  and hconf: "hconf (shr s)"
  and i: "I < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and read: "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! I = ReadMem a'' al'' v"
  and v': "v' \<in> w_values P vs (map NormalAction (take I \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (a'', al'')"
  and ns: "non_speculative P vs (llist_of (map NormalAction (take I \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
  shows "\<exists>ta' xcp'' h'' frs''. P,t \<turnstile> Normal (xcp, shr s, frs) -ta'-jvmd\<rightarrow> Normal (xcp'', h'', frs'') \<and>
           execd_mthr.mthr.if.actions_ok s t ta' \<and> 
           I < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<and> take I \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take I \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> 
           \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! I = ReadMem a'' al'' v' \<and> 
           length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> max jvm_non_speculative_read_bound (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
using assms
apply -
apply(erule jvmd_NormalE)
apply(cases "(P, t, xcp, shr s, frs)" rule: exec.cases)
  apply simp
 defer
 apply simp
apply clarsimp
apply(drule (3) exec_instr_non_speculative_read)
      apply(clarsimp simp add: check_def has_method_def)
     apply simp
    apply(rule i)
   apply(rule read)
  apply(rule v')
 apply(rule ns)
apply(clarsimp simp add: exec_1_d.simps exec_d_def)
done

end

declare split_paired_Ex [simp]
declare eq_upto_seq_inconsist_simps [simp del]

locale JVM_allocated_progress = 
  JVM_progress
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write hconf
    P
  +
  JVM_allocated_heap_conf
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write hconf
    allocated
    P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and P :: "'addr jvm_prog"
begin

lemma non_speculative_read:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and hrt: "heap_read_typeable hconf P"
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "execd_mthr.if.non_speculative_read jvm_non_speculative_read_bound
      (init_fin_lift_state status (JVM_start_state P C M vs)) 
      (w_values P (\<lambda>_. {}) (map snd (lift_start_obs start_tid start_heap_obs)))"
  (is "execd_mthr.if.non_speculative_read _ ?start_state ?start_vs")
proof(rule execd_mthr.if.non_speculative_readI)
  fix ttas s' t x ta x' m' i ad al v v'

  assume \<tau>Red: "execd_mthr.mthr.if.RedT P ?start_state ttas s'"
    and sc: "non_speculative P ?start_vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    and ts't: "thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and red: "execd_mthr.init_fin P t (x, shr s') ta (x', m')"
    and aok: "execd_mthr.mthr.if.actions_ok s' t ta"
    and i: "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    and ns': "non_speculative P (w_values P ?start_vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
    and read: "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v)"
    and v': "v' \<in> w_values P ?start_vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas) @ take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ad, al)"

  from wf_start obtain Ts T meth D where ok: "start_heap_ok"
    and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>meth\<rfloor> in D"
    and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts" by cases

  let ?conv = "\<lambda>ttas. concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)"
  let ?vs' = "w_values P ?start_vs (?conv ttas)"
  let ?wt_ok = "init_fin_lift (\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>)"
  let ?start_obs = "map snd (lift_start_obs start_tid start_heap_obs)"

  from wf obtain wf_md where wf': "wf_prog wf_md P" by(blast dest: wt_jvm_progD)

  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    allocated jvm_known_addrs
    JVM_final "mexecd P" "\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>"
    using wf ok by(rule mexecd_known_addrs_typing)

  from conf have len2: "length vs = length Ts" by(rule list_all2_lengthD)

  from correct_jvm_state_initial[OF wf wf_start]
  have "correct_state_ts \<Phi> (thr (JVM_start_state P C M vs)) start_heap"
    by(simp add: correct_jvm_state_def start_state_def split_beta)
  hence ts_ok_start: "ts_ok ?wt_ok (thr ?start_state) (shr ?start_state)"
    unfolding ts_ok_init_fin_lift_init_fin_lift_state by(simp add: start_state_def split_beta)

  have sc': "non_speculative P ?start_vs (lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of ttas))))"
    using sc by(simp add: lmap_lconcat llist.map_comp o_def split_def lconcat_llist_of[symmetric])
  from start_state_vs_conf[OF wf_prog_wf_syscls[OF wf']]
  have vs_conf_start: "vs_conf P (shr ?start_state) ?start_vs"
    by(simp add:init_fin_lift_state_conv_simps start_state_def split_beta)
  with \<tau>Red ts_ok_start sc
  have wt': "ts_ok ?wt_ok (thr s') (shr s')"
    and vs': "vs_conf P (shr s') ?vs'" by(rule if_RedT_non_speculative_invar)+

  from red i read obtain xcp frs xcp' frs' ta'
    where x: "x = (Running, xcp, frs)" and x': "x' = (Running, xcp', frs')"
    and ta: "ta = convert_TA_initial (convert_obs_initial ta')"
    and red': "P,t \<turnstile> Normal (xcp, shr s', frs) -ta'-jvmd\<rightarrow> Normal (xcp', m', frs')"
    by cases fastforce+

  from ts't wt' x have hconf: "hconf (shr s')" by(auto dest!: ts_okD simp add: correct_state_def)

  have aok': "execd_mthr.mthr.if.actions_ok s' t ta'" using aok unfolding ta by simp
  
  from i read v' ns' ta have "i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" 
    and "\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i = ReadMem ad al v"
    and "v' \<in> w_values P ?vs' (map NormalAction (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) (ad, al)"
    and "non_speculative P ?vs' (llist_of (map NormalAction (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)))"
    by(simp_all add: take_map)

  from exec_1_d_non_speculative_read[OF hrt vs' red' aok' hconf this]
  obtain ta'' xcp'' frs'' h''
    where red'': "P,t \<turnstile> Normal (xcp, shr s', frs) -ta''-jvmd\<rightarrow> Normal (xcp'', h'', frs'')"
    and aok'': "execd_mthr.mthr.if.actions_ok s' t ta''"
    and i'': " i < length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>"
    and eq'': "take i \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
    and read'': "\<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> ! i = ReadMem ad al v'"
    and len'': "length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> \<le> max jvm_non_speculative_read_bound (length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)" by blast

  let ?x' = "(Running, xcp'', frs'')"
  let ?ta' = "convert_TA_initial (convert_obs_initial ta'')"
  from red'' have "execd_mthr.init_fin P t (x, shr s') ?ta' (?x', h'')"
    unfolding x by -(rule execd_mthr.init_fin.NormalAction, simp)
  moreover from aok'' have "execd_mthr.mthr.if.actions_ok s' t ?ta'" by simp
  moreover from i'' have "i < length \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub>" by simp
  moreover from eq'' have "take i \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" unfolding ta by(simp add: take_map)
  moreover from read'' i'' have "\<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v')" by(simp add: nth_map)
  moreover from len'' have "length \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub> \<le> max jvm_non_speculative_read_bound (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)" 
    unfolding ta by simp
  ultimately
  show "\<exists>ta' x'' m''. execd_mthr.init_fin P t (x, shr s') ta' (x'', m'') \<and>
                      execd_mthr.mthr.if.actions_ok s' t ta' \<and>
                      i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<and> take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and>
                      \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v') \<and> 
                      length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> max jvm_non_speculative_read_bound (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
    by blast
qed

lemma JVM_cut_and_update:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and hrt: "heap_read_typeable hconf P" 
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "execd_mthr.if.cut_and_update (init_fin_lift_state status (JVM_start_state P C M vs))
           (mrw_values P Map.empty (map snd (lift_start_obs start_tid start_heap_obs)))"
proof -
  from wf_start obtain Ts T meth D where ok: "start_heap_ok"
    and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>meth\<rfloor> in D"
    and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts" by cases

  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    allocated jvm_known_addrs
    JVM_final "mexecd P" "\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>"
    using wf ok by(rule mexecd_known_addrs_typing)

  let ?start_vs = "w_values P (\<lambda>_. {}) (map snd (lift_start_obs start_tid start_heap_obs))"
  let ?wt_ok = "init_fin_lift (\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>)"
  let ?start_obs = "map snd (lift_start_obs start_tid start_heap_obs)"
  let ?start_state = "init_fin_lift_state status (JVM_start_state P C M vs)"

  from wf obtain wf_md where wf': "wf_prog wf_md P" by(blast dest: wt_jvm_progD)
  hence "wf_syscls P" by(rule wf_prog_wf_syscls)
  moreover
  note non_speculative_read[OF wf hrt wf_start ka]
  moreover have "ts_ok ?wt_ok (thr ?start_state) (shr ?start_state)"
    using correct_jvm_state_initial[OF wf wf_start]
    by(simp add: correct_jvm_state_def start_state_def split_beta)
  moreover have ka: "jvm_known_addrs start_tid ((\<lambda>(mxs, mxl0, b) vs. (None, [([], Null # vs @ replicate mxl0 undefined_value, fst (method P C M), M, 0)])) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
      using ka by(auto simp add: split_beta start_addrs_allocated jvm_known_addrs_def intro: start_tid_start_addrs[OF \<open>wf_syscls P\<close> ok])
  ultimately show ?thesis by(rule non_speculative_read_into_cut_and_update)
qed

lemma JVM_drf:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and hrt: "heap_read_typeable hconf P"
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "drf (JVMd_\<E> P C M vs status) P"
proof -
  from wf_start obtain Ts T meth D where ok: "start_heap_ok"
    and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>meth\<rfloor> in D"
    and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts" by cases

  from wf obtain wf_md where wf': "wf_prog wf_md P" by(blast dest: wt_jvm_progD)
  hence "wf_syscls P" by(rule wf_prog_wf_syscls)
  with JVM_cut_and_update[OF assms]
  show ?thesis
  proof(rule known_addrs_typing.drf[OF mexecd_known_addrs_typing[OF wf ok]])
    from correct_jvm_state_initial[OF wf wf_start]
    show "correct_state_ts \<Phi> (thr (JVM_start_state P C M vs)) start_heap"
      by(simp add: correct_jvm_state_def start_state_def split_beta)
  next
    show "jvm_known_addrs start_tid ((\<lambda>(mxs, mxl0, b) vs. (None, [([], Null # vs @ replicate mxl0 undefined_value, fst (method P C M), M, 0)])) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
      using ka by(auto simp add: split_beta start_addrs_allocated jvm_known_addrs_def intro: start_tid_start_addrs[OF \<open>wf_syscls P\<close> ok])
  qed
qed

lemma JVM_sc_legal:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and hrt: "heap_read_typeable hconf P"
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
shows "sc_legal (JVMd_\<E> P C M vs status) P"
proof -
  from wf_start obtain Ts T meth D where ok: "start_heap_ok"
    and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>meth\<rfloor> in D"
    and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts" by cases

  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    allocated jvm_known_addrs
    JVM_final "mexecd P" "\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>"
    using wf ok by(rule mexecd_known_addrs_typing)

  from wf obtain wf_md where wf': "wf_prog wf_md P" by(blast dest: wt_jvm_progD)
  hence "wf_syscls P" by(rule wf_prog_wf_syscls)

  let ?start_vs = "w_values P (\<lambda>_. {}) (map snd (lift_start_obs start_tid start_heap_obs))"
  let ?wt_ok = "init_fin_lift (\<lambda>t (xcp, frstls) h. \<Phi> \<turnstile> t: (xcp, h, frstls) \<surd>)"
  let ?start_obs = "map snd (lift_start_obs start_tid start_heap_obs)"
  let ?start_state = "init_fin_lift_state status (JVM_start_state P C M vs)"

  note \<open>wf_syscls P\<close> non_speculative_read[OF wf hrt wf_start ka]
  moreover have "ts_ok ?wt_ok (thr ?start_state) (shr ?start_state)"
    using correct_jvm_state_initial[OF wf wf_start]
    by(simp add: correct_jvm_state_def start_state_def split_beta)
  moreover
  have ka_allocated: "jvm_known_addrs start_tid ((\<lambda>(mxs, mxl0, b) vs. (None, [([], Null # vs @ replicate mxl0 undefined_value, fst (method P C M), M, 0)])) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
    using ka by(auto simp add: split_beta start_addrs_allocated jvm_known_addrs_def intro: start_tid_start_addrs[OF \<open>wf_syscls P\<close> ok])
  ultimately have "execd_mthr.if.hb_completion ?start_state (lift_start_obs start_tid start_heap_obs)"
    by(rule non_speculative_read_into_hb_completion)

  thus ?thesis using \<open>wf_syscls P\<close>
  proof(rule sc_legal)
    from correct_jvm_state_initial[OF wf wf_start]
    show "correct_state_ts \<Phi> (thr (JVM_start_state P C M vs)) start_heap"
      by(simp add: correct_jvm_state_def start_state_def split_beta)
  qed(rule ka_allocated)
qed

lemma JVM_jmm_consistent:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and hrt: "heap_read_typeable hconf P"
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "jmm_consistent (JVMd_\<E> P C M vs status) P"
    (is "jmm_consistent ?\<E> P")
proof -
  interpret drf "?\<E>" P using assms by(rule JVM_drf)
  interpret sc_legal "?\<E>" P using assms by(rule JVM_sc_legal)
  show ?thesis by unfold_locales
qed

lemma JVM_ex_sc_exec:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and hrt: "heap_read_typeable hconf P"
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "\<exists>E ws. E \<in> JVMd_\<E> P C M vs status \<and> P \<turnstile> (E, ws) \<surd> \<and> sequentially_consistent P (E, ws)"
  (is "\<exists>E ws. _ \<in> ?\<E> \<and> _")
proof -
  interpret jmm: executions_sc_hb ?\<E> P using assms by -(rule executions_sc)

  let ?start_state = "init_fin_lift_state status (JVM_start_state P C M vs)"
  let ?start_mrw = "mrw_values P Map.empty (map snd (lift_start_obs start_tid start_heap_obs))"

  from execd_mthr.if.sequential_completion_Runs[OF execd_mthr.if.cut_and_update_imp_sc_completion[OF JVM_cut_and_update[OF assms]] ta_seq_consist_convert_RA]
  obtain ttas where Red: "execd_mthr.mthr.if.mthr.Runs P ?start_state ttas"
    and sc: "ta_seq_consist P ?start_mrw (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))" by blast
  let ?E = "lappend (llist_of (lift_start_obs start_tid start_heap_obs)) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ttas))"
  from Red have "?E \<in> ?\<E>" by(blast intro: execd_mthr.mthr.if.\<E>.intros)
  moreover from Red have tsa: "thread_start_actions_ok ?E"
    by(blast intro: execd_mthr.thread_start_actions_ok_init_fin execd_mthr.mthr.if.\<E>.intros)
  from sc have "ta_seq_consist P Map.empty (lmap snd ?E)"
    unfolding lmap_lappend_distrib lmap_lconcat llist.map_comp split_def o_def lmap_llist_of map_map snd_conv
    by(simp add: ta_seq_consist_lappend ta_seq_consist_start_heap_obs)
  from ta_seq_consist_imp_sequentially_consistent[OF tsa jmm.\<E>_new_actions_for_fun[OF \<open>?E \<in> ?\<E>\<close>] this]
  obtain ws where "sequentially_consistent P (?E, ws)" "P \<turnstile> (?E, ws) \<surd>" by iprover
  ultimately show ?thesis by blast
qed

theorem JVM_consistent:
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and hrt: "heap_read_typeable hconf P"
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "\<exists>E ws. legal_execution P (JVMd_\<E> P C M vs status) (E, ws)"
proof -
  let ?\<E> = "JVMd_\<E> P C M vs status"
  interpret sc_legal "?\<E>" P using assms by(rule JVM_sc_legal)
  from JVM_ex_sc_exec[OF assms]
  obtain E ws where "E \<in> ?\<E>" "P \<turnstile> (E, ws) \<surd>" "sequentially_consistent P (E, ws)" by blast
  hence "legal_execution P ?\<E> (E, ws)" by(rule SC_is_legal)
  thus ?thesis by blast
qed

end

text \<open>
  One could now also prove that the aggressive JVM satisfies @{term drf}.
  The key would be that \<open>welltyped_commute\<close> also holds for @{term "non_speculative"} prefixes from start.
\<close>

end
