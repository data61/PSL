(*  Title:      JinjaThreads/Compiler/JVMJ1.thy
    Author:     Andreas Lochbihler
*)

section \<open>Correctness of Stage 2: From JVM to intermediate language\<close>

theory JVMJ1 imports
  J1JVMBisim
begin

declare split_paired_Ex[simp del]

lemma rec_option_is_case_option: "rec_option = case_option"
apply (rule ext)+
apply (rename_tac y)
apply (case_tac y)
apply auto
done

context J1_JVM_heap_base begin

lemma assumes ha: "typeof_addr h a = \<lfloor>Class_type D\<rfloor>"
  and subclsObj: "P \<turnstile> D \<preceq>\<^sup>* Throwable"
  shows bisim1_xcp_\<tau>Red:
  "\<lbrakk> P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
    match_ex_table (compP f P) (cname_of h a) pc (compxE2 e 0 0) = None;
    \<exists>n. n + max_vars e' \<le> length xs \<and> \<B> e n \<rbrakk>
  \<Longrightarrow> \<tau>red1r P t h (e', xs) (Throw a, loc) \<and> P,e,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

  and bisims1_xcp_\<tau>Reds:
  "\<lbrakk> P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>);
     match_ex_table (compP f P) (cname_of h a) pc (compxEs2 es 0 0) = None;
     \<exists>n. n + max_varss es' \<le> length xs \<and> \<B>s es n \<rbrakk>
  \<Longrightarrow> \<exists>vs es''. \<tau>reds1r P t h (es', xs) (map Val vs @ Throw a # es'', loc) \<and>
               P,es,h \<turnstile> (map Val vs @ Throw a # es'', loc) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)"
proof(induct "(e', xs)" "(stk, loc, pc, \<lfloor>a :: 'addr\<rfloor>)"
    and "(es', xs)" "(stk, loc, pc, \<lfloor>a :: 'addr\<rfloor>)"
    arbitrary: e' xs stk loc pc and es' xs stk loc pc rule: bisim1_bisims1.inducts)
  case bisim1NewThrow thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1NewArray thus ?case
    by(auto intro: rtranclp.rtrancl_into_rtrancl New1ArrayThrow bisim1_bisims1.intros dest: bisim1_ThrowD elim!: NewArray_\<tau>red1r_xt)
next
  case bisim1NewArrayThrow thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1NewArrayFail thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1Cast thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl Cast1Throw bisim1_bisims1.intros dest: bisim1_ThrowD elim!: Cast_\<tau>red1r_xt)
next
  case bisim1CastThrow thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1CastFail thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1InstanceOf thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl InstanceOf1Throw bisim1_bisims1.intros dest: bisim1_ThrowD elim!: InstanceOf_\<tau>red1r_xt)
next
  case bisim1InstanceOfThrow thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1BinOp1 thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl Bin1OpThrow1 bisim1_bisims1.intros simp add: match_ex_table_append dest: bisim1_ThrowD elim!: BinOp_\<tau>red1r_xt1)
next
  case bisim1BinOp2 thus ?case
    by(clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_shift_pc_None)
      (fastforce intro: rtranclp.rtrancl_into_rtrancl red1_reds1.intros bisim1BinOpThrow2 elim!: BinOp_\<tau>red1r_xt2)
next
  case bisim1BinOpThrow1 thus ?case
    by(auto simp add: match_ex_table_append intro: bisim1_bisims1.intros)
next
  case (bisim1BinOpThrow2 e xs stk loc pc e1 bop)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with bisim show ?case
    by(auto intro: bisim1_bisims1.bisim1BinOpThrow2)
next
  case bisim1BinOpThrow thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1LAss1 thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl LAss1Throw bisim1_bisims1.intros dest: bisim1_ThrowD elim!: LAss_\<tau>red1r)
next
  case bisim1LAssThrow thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1AAcc1 thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl AAcc1Throw1 bisim1_bisims1.intros simp add: match_ex_table_append dest: bisim1_ThrowD elim!: AAcc_\<tau>red1r_xt1)
next
  case bisim1AAcc2 thus ?case
    by(clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_shift_pc_None)
      (fastforce intro: rtranclp.rtrancl_into_rtrancl red1_reds1.intros bisim1AAccThrow2 elim!: AAcc_\<tau>red1r_xt2)
next
  case bisim1AAccThrow1 thus ?case
    by(auto simp add: match_ex_table_append intro: bisim1_bisims1.intros)
next
  case bisim1AAccThrow2 thus ?case
    by(auto simp add: match_ex_table_append intro: bisim1_bisims1.intros dest: bisim1_ThrowD)
next
  case bisim1AAccFail thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1AAss1 thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl AAss1Throw1 bisim1_bisims1.intros simp add: match_ex_table_append dest: bisim1_ThrowD elim!: AAss_\<tau>red1r_xt1)
next
  case bisim1AAss2 thus ?case
    by(clarsimp simp add: compxE2_size_convs compxE2_stack_xlift_convs)
      (fastforce simp add: match_ex_table_append intro: rtranclp.rtrancl_into_rtrancl red1_reds1.intros bisim1AAssThrow2 elim!: AAss_\<tau>red1r_xt2)
next
  case bisim1AAss3 thus ?case
    by(clarsimp simp add: compxE2_size_convs compxE2_stack_xlift_convs)
      (fastforce simp add: match_ex_table_append intro: rtranclp.rtrancl_into_rtrancl red1_reds1.intros bisim1AAssThrow3 elim!: AAss_\<tau>red1r_xt3)
next
  case bisim1AAssThrow1 thus ?case
    by(auto simp add: match_ex_table_append intro: bisim1_bisims1.intros)
next
  case (bisim1AAssThrow2 e xs stk loc pc i e2)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with bisim show ?case
    by(auto intro: bisim1_bisims1.bisim1AAssThrow2)
next
  case (bisim1AAssThrow3 e xs stk loc pc A i)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with bisim show ?case
    by(auto intro: bisim1_bisims1.bisim1AAssThrow3)
next
  case bisim1AAssFail thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1ALength thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl ALength1Throw bisim1_bisims1.intros dest: bisim1_ThrowD elim!: ALength_\<tau>red1r_xt)
next
  case bisim1ALengthThrow thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1ALengthNull thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1FAcc thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl FAcc1Throw bisim1_bisims1.intros dest: bisim1_ThrowD elim!: FAcc_\<tau>red1r_xt)
next
  case bisim1FAccThrow thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1FAccNull thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1FAss1 thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl FAss1Throw1 bisim1_bisims1.intros simp add: match_ex_table_append dest: bisim1_ThrowD elim!: FAss_\<tau>red1r_xt1)
next
  case bisim1FAss2 thus ?case
    by(clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxE2_stack_xlift_convs)
      (fastforce intro: rtranclp.rtrancl_into_rtrancl red1_reds1.intros bisim1FAssThrow2 elim!: FAss_\<tau>red1r_xt2)
next
  case bisim1FAssThrow1 thus ?case
    by(auto simp add: match_ex_table_append intro: bisim1_bisims1.intros)
next
  case (bisim1FAssThrow2 e2 xs stk loc pc e)
  note bisim = \<open>P,e2,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with bisim show ?case
    by(auto intro: bisim1_bisims1.bisim1FAssThrow2)
next
  case bisim1FAssNull thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1CAS1 thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl CAS1Throw bisim1_bisims1.intros simp add: match_ex_table_append dest: bisim1_ThrowD elim!: CAS_\<tau>red1r_xt1)
next
  case bisim1CAS2 thus ?case
    by(clarsimp simp add: compxE2_size_convs compxE2_stack_xlift_convs)
      (fastforce simp add: match_ex_table_append intro: rtranclp.rtrancl_into_rtrancl red1_reds1.intros bisim1CASThrow2 elim!: CAS_\<tau>red1r_xt2)
next
  case bisim1CAS3 thus ?case
    by(clarsimp simp add: compxE2_size_convs compxE2_stack_xlift_convs)
      (fastforce simp add: match_ex_table_append intro: rtranclp.rtrancl_into_rtrancl red1_reds1.intros bisim1CASThrow3 elim!: CAS_\<tau>red1r_xt3)
next
  case bisim1CASThrow1 thus ?case
    by(auto simp add: match_ex_table_append intro: bisim1_bisims1.intros)
next
  case (bisim1CASThrow2 e xs stk loc pc i e2)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with bisim show ?case
    by(auto intro: bisim1_bisims1.bisim1CASThrow2)
next
  case (bisim1CASThrow3 e xs stk loc pc A i)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with bisim show ?case
    by(auto intro: bisim1_bisims1.bisim1CASThrow3)
next
  case bisim1CASFail thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1Call1 thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl Call1ThrowObj bisim1_bisims1.intros simp add: match_ex_table_append dest: bisim1_ThrowD elim!: Call_\<tau>red1r_obj)
next
  case bisim1CallParams thus ?case
    by(clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxEs2_size_convs compxE2_stack_xlift_convs compxEs2_stack_xlift_convs match_ex_table_shift_pc_None)
      (fastforce intro: rtranclp.rtrancl_into_rtrancl Call1ThrowParams[OF refl] bisim1CallThrowParams elim!: Call_\<tau>red1r_param)
next
  case bisim1CallThrowObj thus ?case
    by(auto simp add: match_ex_table_append intro: bisim1_bisims1.intros)
next
  case (bisim1CallThrowParams es vs es' xs stk loc pc obj M)
  note bisim = \<open>P,es,h \<turnstile> (map Val vs @ Throw a # es', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  hence "xs = loc" by(auto dest: bisims1_ThrowD)
  with bisim show ?case
    by(auto intro: bisim1_bisims1.bisim1CallThrowParams)
next
  case bisim1CallThrow thus ?case
    by(auto intro: bisim1_bisims1.intros)
next
  case (bisim1BlockSome4 e e' xs stk loc pc V Ty v)
  from \<open>\<exists>n. n + max_vars {V:Ty=None; e'} \<le> length xs \<and> \<B> {V:Ty=\<lfloor>v\<rfloor>; e} n\<close>
  have V: "V < length xs" by simp
  from bisim1BlockSome4 have Red: "\<tau>red1r P t h (e', xs) (Throw a, loc)"
    and bisim: "P,e,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(auto simp add: match_ex_table_append_not_pcs compxE2_size_convs compxEs2_size_convs compxE2_stack_xlift_convs compxEs2_stack_xlift_convs match_ex_table_shift_pc_None intro!: exI[where x="Suc V"] elim: meta_impE)
  note len = \<tau>red1r_preserves_len[OF Red]
  from Red have "\<tau>red1r P t h ({V:Ty=None; e'}, xs) ({V:Ty=None; Throw a}, loc)" by(auto intro: Block_None_\<tau>red1r_xt)
  thus ?case using V len bisim 
    by(auto intro: \<tau>move1BlockThrow Block1Throw bisim1BlockThrowSome elim!: rtranclp.rtrancl_into_rtrancl)
next
  case bisim1BlockThrowSome thus ?case
    by(auto dest: bisim1_ThrowD intro: bisim1_bisims1.bisim1BlockThrowSome)
next
  case (bisim1BlockNone e e' xs stk loc pc V Ty)
  hence Red: "\<tau>red1r P t h (e', xs) (Throw a, loc)"
    and bisim: "P,e,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(auto elim: meta_impE intro!: exI[where x="Suc V"])
  from Red have len: "length loc = length xs" by(rule \<tau>red1r_preserves_len)
  from \<open>\<exists>n. n + max_vars {V:Ty=None; e'} \<le> length xs \<and> \<B> {V:Ty=None; e} n\<close>
  have V: "V < length xs" by simp
  from Red have "\<tau>red1r P t h ({V:Ty=None; e'}, xs) ({V:Ty=None; Throw a}, loc)" by(rule Block_None_\<tau>red1r_xt)
  thus ?case using V len bisim
    by(auto intro: \<tau>move1BlockThrow Block1Throw bisim1BlockThrowNone elim!: rtranclp.rtrancl_into_rtrancl)
next
  case bisim1BlockThrowNone thus ?case
    by(auto dest: bisim1_ThrowD intro: bisim1_bisims1.bisim1BlockThrowNone)
next
  case bisim1Sync1 thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl Synchronized1Throw1 bisim1_bisims1.intros simp add: match_ex_table_append dest: bisim1_ThrowD elim!: Sync_\<tau>red1r_xt)
next
  case (bisim1Sync4 e2 e' xs stk loc pc V e1 a')
  from \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  have "pc < length (compE2 e2)" by(auto dest!: bisim1_xcp_pcD)
  with \<open>match_ex_table (compP f P) (cname_of h a) (Suc (Suc (Suc (length (compE2 e1) + pc)))) (compxE2 (sync\<^bsub>V\<^esub> (e1) e2) 0 0) = None\<close> subclsObj ha
  have False by(simp add: match_ex_table_append matches_ex_entry_def split: if_split_asm)
  thus ?case ..
next
  case bisim1Sync10 thus ?case 
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1Sync11 thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1Sync12 thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1Sync14 thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1SyncThrow thus ?case
    by(auto simp add: match_ex_table_append intro: bisim1_bisims1.intros)
next
  case bisim1Seq1 thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl Seq1Throw bisim1_bisims1.intros dest: bisim1_ThrowD elim!: Seq_\<tau>red1r_xt simp add: match_ex_table_append)
next
  case bisim1SeqThrow1 thus ?case
    by(auto simp add: match_ex_table_append intro: bisim1_bisims1.intros)
next
  case bisim1Seq2 thus ?case
    by(auto simp add: match_ex_table_append_not_pcs compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_shift_pc_None intro: bisim1_bisims1.bisim1Seq2)
next
  case bisim1Cond1 thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl Cond1Throw bisim1_bisims1.intros dest: bisim1_ThrowD elim!: Cond_\<tau>red1r_xt simp add: match_ex_table_append)
next
  case bisim1CondThen thus ?case
    by(clarsimp simp add: match_ex_table_append)
     (auto simp add: match_ex_table_append_not_pcs compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_shift_pc_None intro: bisim1_bisims1.bisim1CondThen)
next
  case bisim1CondElse thus ?case
    by(clarsimp simp add: match_ex_table_append)
      (auto simp add: match_ex_table_append_not_pcs compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_shift_pc_None intro: bisim1_bisims1.bisim1CondElse)
next
  case bisim1CondThrow thus ?case
    by(auto simp add: match_ex_table_append intro: bisim1_bisims1.intros)
next
  case bisim1While3 thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl Cond1Throw bisim1_bisims1.intros dest: bisim1_ThrowD elim!: Cond_\<tau>red1r_xt simp add: match_ex_table_append)
next
  case (bisim1While4 e e' xs stk loc pc c)
  hence "\<tau>red1r P t h (e', xs) (Throw a, loc) \<and> P,e,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(auto simp add: match_ex_table_append_not_pcs compxE2_size_convs compxEs2_size_convs compxE2_stack_xlift_convs compxEs2_stack_xlift_convs match_ex_table_shift_pc_None)
  hence "\<tau>red1r P t h (e';;while (c) e, xs) (Throw a, loc)"
    "P,while (c) e,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, Suc (length (compE2 c) + pc), \<lfloor>a\<rfloor>)"
    by(auto intro: rtranclp.rtrancl_into_rtrancl Seq1Throw \<tau>move1SeqThrow bisim1WhileThrow2 elim!: Seq_\<tau>red1r_xt)
  thus ?case ..
next
  case bisim1WhileThrow1 thus ?case
    by(auto simp add: match_ex_table_append intro: bisim1_bisims1.intros)
next
  case bisim1WhileThrow2 thus ?case
    by(auto simp add: match_ex_table_append intro: bisim1_bisims1.intros dest: bisim1_ThrowD)
next
  case bisim1Throw1 thus ?case
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl Throw1Throw bisim1_bisims1.intros dest: bisim1_ThrowD elim!: Throw_\<tau>red1r_xt)
next
  case bisim1Throw2 thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1ThrowNull thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case bisim1ThrowThrow thus ?case
    by(fastforce intro: bisim1_bisims1.intros)
next
  case (bisim1Try e e' xs stk loc pc C V e2)
  hence red: "\<tau>red1r P t h (e', xs) (Throw a, loc)"
    and bisim: "P,e,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(auto simp add: match_ex_table_append)
  from red have Red: "\<tau>red1r P t h (try e' catch(C V) e2, xs) (try Throw a catch(C V) e2, loc)" by(rule Try_\<tau>red1r_xt)
  from \<open>match_ex_table (compP f P) (cname_of h a) pc (compxE2 (try e catch(C V) e2) 0 0) = None\<close>
  have "\<not> matches_ex_entry (compP f P) (cname_of h a) pc (0, length (compE2 e), \<lfloor>C\<rfloor>, Suc (length (compE2 e)), 0)"
    by(auto simp add: match_ex_table_append split: if_split_asm)
  moreover from \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  have "pc < length (compE2 e)" by(auto dest: bisim1_xcp_pcD)
  ultimately have subcls: "\<not> P \<turnstile> D \<preceq>\<^sup>* C" using ha by(simp add: matches_ex_entry_def cname_of_def)
  with ha have "True,P,t \<turnstile>1 \<langle>try Throw a catch(C V) e2, (h, loc)\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, (h, loc)\<rangle>"
    by -(rule Red1TryFail, auto)
  moreover from bisim ha subcls
  have "P,try e catch(C V) e2,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(rule bisim1TryFail)
  ultimately show ?case using Red by(blast intro: rtranclp.rtrancl_into_rtrancl \<tau>move1TryThrow)
next
  case (bisim1TryCatch2 e2 e' xs stk loc pc e1 C V)
  hence *: "\<tau>red1r P t h (e', xs) (Throw a, loc) \<and> P,e2,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(clarsimp simp add: match_ex_table_append matches_ex_entry_def split: if_split_asm)
      (auto simp add: match_ex_table_append compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_shift_pc_None elim: meta_impE intro!: exI[where x="Suc V"])
  moreover note \<tau>red1r_preserves_len[OF *[THEN conjunct1]]
  moreover from \<open>\<exists>n. n + max_vars {V:Class C=None; e'} \<le> length xs \<and> \<B> (try e1 catch(C V) e2) n\<close>
  have "V < length xs" by simp
  ultimately show ?case 
    by(fastforce intro: rtranclp.rtrancl_into_rtrancl Block1Throw \<tau>move1BlockThrow bisim1TryCatchThrow elim!: Block_None_\<tau>red1r_xt)
next
  case (bisim1TryFail e xs stk loc pc C'' C' V e2)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with bisim \<open>typeof_addr h a = \<lfloor>Class_type C''\<rfloor>\<close> \<open>\<not> P \<turnstile> C'' \<preceq>\<^sup>* C'\<close>
  show ?case by(auto intro: bisim1_bisims1.bisim1TryFail)
next
  case (bisim1TryCatchThrow e2 xs stk loc pc e C' V)
  from \<open>P,e2,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close> have "xs = loc"
    by(auto dest: bisim1_ThrowD)
  with \<open>P,e2,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close> show ?case
    by(auto intro: bisim1_bisims1.bisim1TryCatchThrow)
next
  case (bisims1List1 e e' xs stk loc pc es)
  hence "\<tau>red1r P t h (e', xs) (Throw a, loc)"
    and bisim: "P,e,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)" by(auto simp add: match_ex_table_append)
  hence "\<tau>reds1r P t h (e' # es, xs) (map Val [] @ Throw a # es, loc)" by(auto intro: \<tau>red1r_inj_\<tau>reds1r)
  moreover from bisim
  have "P,e#es,h \<turnstile> (Throw a # es, loc) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(rule bisim1_bisims1.bisims1List1)
  ultimately show ?case by fastforce
next
  case (bisims1List2 es es' xs stk loc pc e v)
  hence "\<exists>vs es''. \<tau>reds1r P t h (es', xs) (map Val vs @ Throw a # es'', loc) \<and> P,es,h \<turnstile> (map Val vs @ Throw a # es'', loc) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(auto simp add: match_ex_table_append_not_pcs compxEs2_size_convs compxEs2_stack_xlift_convs match_ex_table_shift_pc_None)
  then obtain vs es'' where red: "\<tau>reds1r P t h (es', xs) (map Val vs @ Throw a # es'', loc)" 
    and bisim: "P,es,h \<turnstile> (map Val vs @ Throw a # es'', loc) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)" by blast
  from red have "\<tau>reds1r P t h (Val v # es', xs) (map Val (v # vs) @ Throw a # es'', loc)"
    by(auto intro: \<tau>reds1r_cons_\<tau>reds1r)
  moreover from bisim 
  have "P,e # es,h \<turnstile> (map Val (v # vs) @ Throw a # es'', loc) [\<leftrightarrow>] (stk @ [v], loc, length (compE2 e) + pc, \<lfloor>a\<rfloor>)"
    by(auto intro: bisim1_bisims1.bisims1List2)
  ultimately show ?case by fastforce
qed

primrec conf_xcp' :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr option \<Rightarrow> bool" where
  "conf_xcp' P h None = True"
| "conf_xcp' P h \<lfloor>a\<rfloor> = (\<exists>D. typeof_addr h a = \<lfloor>Class_type D\<rfloor> \<and> P \<turnstile> D \<preceq>\<^sup>* Throwable)"

lemma conf_xcp_conf_xcp':
  "conf_xcp P h xcp i \<Longrightarrow> conf_xcp' P h xcp"
by(cases xcp) auto

lemma conf_xcp'_compP [simp]: "conf_xcp' (compP f P) = conf_xcp' P"
by(clarsimp simp add: fun_eq_iff conf_xcp'_def rec_option_is_case_option)

end

context J1_heap_base begin

lemmas \<tau>red1_Val_simps [simp] =
  \<tau>red1r_Val \<tau>red1t_Val \<tau>reds1r_map_Val \<tau>reds1t_map_Val

end

context J1_JVM_conf_read begin

lemma assumes wf: "wf_J1_prog P"
  and hconf: "hconf h" "preallocated h"
  and tconf: "P,h \<turnstile> t \<surd>t"
  shows red1_simulates_exec_instr:
  "\<lbrakk> P, E, h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp);
     exec_move_d P t E h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp');
     n + max_vars e \<le> length xs; bsok E n; P,h \<turnstile> stk [:\<le>] ST; conf_xcp' (compP2 P) h xcp \<rbrakk>
  \<Longrightarrow> \<exists>e'' xs''. P, E, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and>
     (if \<tau>move2 (compP2 P) h stk E pc xcp
      then h' = h \<and> (if xcp' = None \<longrightarrow> pc < pc' then \<tau>red1r else \<tau>red1t) P t h (e, xs) (e'', xs'')
      else \<exists>ta' e' xs'. \<tau>red1r P t h (e, xs) (e', xs') \<and> True,P,t \<turnstile>1 \<langle>e', (h, xs')\<rangle> -ta'\<rightarrow> \<langle>e'', (h', xs'')\<rangle> \<and> ta_bisim wbisim1 (extTA2J1 P ta') ta \<and> \<not> \<tau>move1 P h e' \<and> (call1 e = None \<or> no_call2 E pc \<or> e' = e \<and> xs' = xs))"
  (is "\<lbrakk> _; ?exec E stk loc pc xcp stk' loc' pc' xcp'; _; _; _; _ \<rbrakk>
       \<Longrightarrow> \<exists>e'' xs''. P, E, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e xs e'' xs'' E stk pc pc' xcp xcp'")

  and reds1_simulates_exec_instr:
  "\<lbrakk> P, Es, h \<turnstile> (es, xs) [\<leftrightarrow>] (stk, loc, pc, xcp);
     exec_moves_d P t Es h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp');
     n + max_varss es \<le> length xs; bsoks Es n; P,h \<turnstile> stk [:\<le>] ST; conf_xcp' (compP2 P) h xcp \<rbrakk>
  \<Longrightarrow> \<exists>es'' xs''. P, Es, h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk', loc', pc', xcp') \<and>
     (if \<tau>moves2 (compP2 P) h stk Es pc xcp
      then h' = h \<and> (if xcp' = None \<longrightarrow> pc < pc' then \<tau>reds1r else \<tau>reds1t) P t h (es, xs) (es'', xs'')
      else \<exists>ta' es' xs'. \<tau>reds1r P t h (es, xs) (es', xs') \<and> True,P,t \<turnstile>1 \<langle>es', (h, xs')\<rangle> [-ta'\<rightarrow>] \<langle>es'', (h', xs'')\<rangle> \<and> ta_bisim wbisim1 (extTA2J1 P ta') ta \<and> \<not> \<tau>moves1 P h es' \<and> (calls1 es = None \<or> no_calls2 Es pc \<or> es' = es \<and> xs' = xs))"
  (is "\<lbrakk> _; ?execs Es stk loc pc xcp stk' loc' pc' xcp'; _; _; _; _ \<rbrakk>
       \<Longrightarrow> \<exists>es'' xs''. P, Es, h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk', loc', pc', xcp') \<and> ?reds es xs es'' xs'' Es stk pc pc' xcp xcp'")
proof(induction E n e xs stk loc pc xcp and Es n es xs stk loc pc xcp
    arbitrary: stk' loc' pc' xcp' ST and stk' loc' pc' xcp' ST rule: bisim1_bisims1_inducts_split)
  case (bisim1Val2 e n v xs)
  from \<open>?exec e [v] xs (length (compE2 e)) None stk' loc' pc' xcp'\<close>
  have False by(auto dest: exec_meth_length_compE2D simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1New C' n xs)
  note exec = \<open>exec_move_d P t (new C') h ([], xs, 0, None) ta h' (stk', loc', pc', xcp')\<close>
  have \<tau>: "\<not> \<tau>move2 (compP2 P) h [] (new C') 0 None" "\<not> \<tau>move1 P h (new C')" by(auto simp add: \<tau>move2_iff)
  show ?case
  proof(cases "allocate h (Class_type C') = {}")
    case True
    have "P,new C',h' \<turnstile> (THROW OutOfMemory, xs) \<leftrightarrow> ([], xs, 0, \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"
      by(rule bisim1NewThrow)
    with exec \<tau> True show ?thesis
      by(fastforce intro: Red1NewFail elim!: exec_meth.cases simp add: exec_move_def)
  next
    case False
    have "\<And>a h'. P,new C',h' \<turnstile> (addr a, xs) \<leftrightarrow> ([Addr a], xs, length (compE2 (new C')), None)"
      by(rule bisim1Val2) auto
    thus ?thesis using exec False \<tau>
      apply(simp add: exec_move_def)
      apply(erule exec_meth.cases)
      apply simp_all
      apply clarsimp
      apply(auto intro!: Red1New exI simp add: ta_bisim_def)
      done
  qed
next
  case (bisim1NewThrow C' n xs)
  from \<open>?exec (new C') [] xs 0 \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor> stk' loc' pc' xcp'\<close>
  have False by(auto elim: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1NewArray e n e' xs stk loc pc xcp U)
  note IH = bisim1NewArray.IH(2)
  note exec = \<open>?exec (newA U\<lfloor>e\<rceil>) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars (newA U\<lfloor>e'\<rceil>) \<le> length xs\<close>
  note bsok = \<open>bsok (newA U\<lfloor>e\<rceil>) n\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'"
      by(auto simp add: exec_move_newArray)
    from True have "\<tau>move2 (compP2 P) h stk (newA U\<lfloor>e\<rceil>) pc xcp = \<tau>move2 (compP2 P) h stk e pc xcp" by(simp add: \<tau>move2_iff)
    moreover have "no_call2 e pc \<Longrightarrow> no_call2 (newA U\<lfloor>e\<rceil>) pc" by(simp add: no_call2_def)
    ultimately show ?thesis using IH[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok
      by(fastforce intro: bisim1_bisims1.bisim1NewArray New1ArrayRed elim!: NewArray_\<tau>red1r_xt NewArray_\<tau>red1t_xt)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (newA U\<lfloor>e'\<rceil>, xs) (newA U\<lfloor>Val v\<rceil>, loc)" by(rule NewArray_\<tau>red1r_xt)
    moreover have \<tau>: "\<not> \<tau>move2 (compP2 P) h [v] (newA U\<lfloor>e\<rceil>) pc None" by(simp add: \<tau>move2_iff)
    moreover have "\<not> \<tau>move1 P h (newA U\<lfloor>Val v\<rceil>)" by auto
    moreover from exec stk xcp obtain I
      where [simp]: "v = Intg I" by(auto elim!: exec_meth.cases simp add: exec_move_def)
    have "\<exists>ta' e''. P,newA U\<lfloor>e\<rceil>,h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> True,P,t \<turnstile>1 \<langle>newA U\<lfloor>Val v\<rceil>,(h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim wbisim1 (extTA2J1 P ta') ta"
    proof(cases "I <s 0")
      case True with exec stk xcp show ?thesis
        by(fastforce elim!: exec_meth.cases intro: bisim1NewArrayFail Red1NewArrayNegative simp add: exec_move_def)
    next
      case False
      show ?thesis
      proof(cases "allocate h (Array_type U (nat (sint I))) = {}")
        case True
        with False exec stk xcp show ?thesis
          by(fastforce elim!: exec_meth.cases intro: bisim1NewArrayFail Red1NewArrayFail simp add: exec_move_def)
      next
        case False
        have "\<And>a h'. P,newA U\<lfloor>e\<rceil>,h' \<turnstile> (addr a, loc) \<leftrightarrow> ([Addr a], loc, length (compE2 (newA U\<lfloor>e\<rceil>)), None)"
          by(rule bisim1Val2) simp
        with False \<open>\<not> I <s 0\<close> exec stk xcp show ?thesis
          apply(simp add: exec_move_def)
          apply(erule exec_meth.cases)
          apply simp_all
          apply clarsimp
          apply(auto intro!: Red1NewArray exI simp add: ta_bisim_def)
          done
      qed
    qed
    moreover have "no_call2 (newA U\<lfloor>e\<rceil>) pc" by(simp add: no_call2_def)
    ultimately show ?thesis using exec stk xcp by fastforce
  qed
next
  case (bisim1NewArrayThrow e n a xs stk loc pc U)
  note exec = \<open>?exec (newA U\<lfloor>e\<rceil>) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False by (auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1NewArrayFail e n U a xs v)
  note exec = \<open>?exec (newA U\<lfloor>e\<rceil>) [v] xs (length (compE2 e)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  hence False by(auto elim!: exec_meth.cases dest: match_ex_table_pc_length_compE2 simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1Cast e n e' xs stk loc pc xcp U)
  note IH = bisim1Cast.IH(2)
  note exec = \<open>?exec (Cast U e) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars (Cast U e') \<le> length xs\<close>
  note ST = \<open>P,h \<turnstile> stk [:\<le>] ST\<close>
  note bsok = \<open>bsok (Cast U e) n\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'" by(auto simp add: exec_move_Cast)
    from True have "\<tau>move2 (compP2 P) h stk (Cast U e) pc xcp = \<tau>move2 (compP2 P) h stk e pc xcp" by(simp add: \<tau>move2_iff)
    moreover have "no_call2 e pc \<Longrightarrow> no_call2 (Cast U e) pc" by(simp add: no_call2_def)
    ultimately show ?thesis using IH[OF exec' _ _ ST \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok
      by(fastforce intro: bisim1_bisims1.bisim1Cast Cast1Red elim!: Cast_\<tau>red1r_xt Cast_\<tau>red1t_xt)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (Cast U e', xs) (Cast U (Val v), loc)" by(rule Cast_\<tau>red1r_xt)
    also from exec have [simp]: "h' = h" "ta = \<epsilon>" by(auto simp add: exec_move_def elim!: exec_meth.cases split: if_split_asm)
    have "\<exists>e''. P,Cast U e,h \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> True,P,t \<turnstile>1 \<langle>Cast U (Val v),(h, loc)\<rangle> -\<epsilon>\<rightarrow> \<langle>e'',(h, loc)\<rangle>"
    proof(cases "P \<turnstile> the (typeof\<^bsub>h\<^esub> v) \<le> U")
      case False with exec stk xcp bsok ST show ?thesis
        by(fastforce simp add: compP2_def exec_move_def exec_meth_instr list_all2_Cons1 conf_def intro: bisim1CastFail Red1CastFail)
    next
      case True
      have "P,Cast U e,h \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (Cast U e)), None)"
          by(rule bisim1Val2) simp
      with exec stk xcp ST True show ?thesis
        by(fastforce simp add: compP2_def exec_move_def exec_meth_instr list_all2_Cons1 conf_def intro: Red1Cast)
    qed
    then obtain e'' where bisim': "P,Cast U e,h \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "True,P,t \<turnstile>1 \<langle>Cast U (Val v),(h, loc)\<rangle> -\<epsilon>\<rightarrow> \<langle>e'',(h, loc)\<rangle>" by blast
    have "\<tau>move1 P h (Cast U (Val v))" by(rule \<tau>move1CastRed)
    with red have "\<tau>red1t P t h (Cast U (Val v), loc) (e'', loc)" by(auto intro: \<tau>red1t_1step)
    also have \<tau>: "\<tau>move2 (compP2 P) h [v] (Cast U e) pc None" by(simp add: \<tau>move2_iff)
    moreover have "no_call2 (Cast U e) pc" by(simp add: no_call2_def)
    ultimately show ?thesis using exec stk xcp bisim' by fastforce
  qed
next
  case (bisim1CastThrow e n a xs stk loc pc U)
  note exec = \<open>?exec (Cast U e) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False by (auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1CastFail e n U xs v)
  note exec = \<open>?exec (Cast U e) [v] xs (length (compE2 e)) \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor> stk' loc' pc' xcp'\<close>
  hence False by(auto elim!: exec_meth.cases dest: match_ex_table_pc_length_compE2 simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1InstanceOf e n e' xs stk loc pc xcp U)
  note IH = bisim1InstanceOf.IH(2)
  note exec = \<open>?exec (e instanceof U) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars (e' instanceof U) \<le> length xs\<close>
  note ST = \<open>P,h \<turnstile> stk [:\<le>] ST\<close>
  note bsok = \<open>bsok (e instanceof U) n\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'" by(auto simp add: exec_move_InstanceOf)
    from True have "\<tau>move2 (compP2 P) h stk (e instanceof U) pc xcp = \<tau>move2 (compP2 P) h stk e pc xcp"
      by(simp add: \<tau>move2_iff)
    moreover have "no_call2 e pc \<Longrightarrow> no_call2 (e instanceof U) pc" by(simp add: no_call2_def)
    ultimately show ?thesis using IH[OF exec' _ _ ST \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok
      by(fastforce intro: bisim1_bisims1.bisim1InstanceOf InstanceOf1Red elim!: InstanceOf_\<tau>red1r_xt InstanceOf_\<tau>red1t_xt)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (e' instanceof U, xs) ((Val v) instanceof U, loc)" by(rule InstanceOf_\<tau>red1r_xt)
    also let ?v = "Bool (v \<noteq> Null \<and> P \<turnstile> the (typeof\<^bsub>h\<^esub> v) \<le> U)"
    from exec ST stk xcp have [simp]: "h' = h" "ta = \<epsilon>" "xcp' = None" "loc' = loc" "stk' = [?v]" "pc' = Suc pc"
      by(auto simp add: exec_move_def list_all2_Cons1 conf_def compP2_def elim!: exec_meth.cases split: if_split_asm)
    have bisim': "P,e instanceof U,h \<turnstile> (Val ?v, loc) \<leftrightarrow> ([?v], loc, length (compE2 (e instanceof U)), None)"
      by(rule bisim1Val2) simp
    from exec stk xcp ST
    have red: "True,P,t \<turnstile>1 \<langle>(Val v) instanceof U,(h, loc)\<rangle> -\<epsilon>\<rightarrow> \<langle>Val ?v ,(h, loc)\<rangle>"
      by(auto simp add: compP2_def exec_move_def exec_meth_instr list_all2_Cons1 conf_def intro: Red1InstanceOf)
    have "\<tau>move1 P h ((Val v) instanceof U)" by(rule \<tau>move1InstanceOfRed)
    with red have "\<tau>red1t P t h ((Val v) instanceof U, loc) (Val ?v, loc)" by(auto intro: \<tau>red1t_1step)
    also have \<tau>: "\<tau>move2 (compP2 P) h [v] (e instanceof U) pc None" by(simp add: \<tau>move2_iff)
    moreover have "no_call2 (e instanceof U) pc" by(simp add: no_call2_def)
    ultimately show ?thesis using exec stk xcp bisim' by(fastforce)
  qed
next
  case (bisim1InstanceOfThrow e n a xs stk loc pc U)
  note exec = \<open>?exec (e instanceof U) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False by (auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1Val v n xs)
  from \<open>?exec (Val v) [] xs 0 None stk' loc' pc' xcp'\<close>
  have "stk' = [v]" "loc' = xs" "h' = h" "pc' = length (compE2 (Val v))" "xcp' = None"
    by(auto elim: exec_meth.cases simp add: exec_move_def)
  moreover have "P,Val v,h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, length (compE2 (Val v)), None)"
    by(rule bisim1Val2) simp
  moreover have "\<tau>move2 (compP2 P) h [] (Val v) 0 None" by(rule \<tau>move2Val)
  ultimately show ?case by(auto)
next
  case (bisim1Var V n xs)
  note exec = \<open>?exec (Var V) [] xs 0 None stk' loc' pc' xcp'\<close>
  moreover note len = \<open>n + max_vars (Var V) \<le> length xs\<close>
  moreover have "\<tau>move2 (compP2 P) h [] (Var V) 0 None" "\<tau>move1 P h (Var V)"
    by(auto intro: \<tau>move1Var simp add: \<tau>move2_iff)
  moreover have "P,Var V,h \<turnstile> (Val (xs ! V), xs) \<leftrightarrow> ([xs ! V], xs, length (compE2 (Var V)), None)"
    by(rule bisim1Val2) simp
  ultimately show ?case by(fastforce elim!: exec_meth.cases intro: Red1Var r_into_rtranclp simp add: exec_move_def)
next
  case (bisim1BinOp1 e1 n e1' xs stk loc pc xcp e2 bop)
  note IH1 = bisim1BinOp1.IH(2)
  note IH2 = bisim1BinOp1.IH(4)
  note exec = \<open>?exec (e1 \<guillemotleft>bop\<guillemotright> e2) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note len = \<open>n + max_vars (e1' \<guillemotleft>bop\<guillemotright> e2) \<le> length xs\<close>
  note ST = \<open>P,h \<turnstile> stk [:\<le>] ST\<close>
  note bsok = \<open>bsok (e1 \<guillemotleft>bop\<guillemotright> e2) n\<close>
  from bisim1 have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    with exec have exec': "?exec e1 stk loc pc xcp stk' loc' pc' xcp'" by(auto simp add: exec_move_BinOp1)
    from True have \<tau>: "\<tau>move2 (compP2 P) h stk (e1 \<guillemotleft>bop\<guillemotright> e2) pc xcp = \<tau>move2 (compP2 P) h stk e1 pc xcp"
      by(simp add: \<tau>move2_iff)
    with IH1[OF exec' _ _ ST \<open>conf_xcp' (compP2 P) h xcp\<close>] bisim2 len bsok obtain e'' xs''
      where bisim': "P,e1,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red e1' xs e'' xs'' e1 stk pc pc' xcp xcp'" by auto
    from bisim' have "P,e1 \<guillemotleft>bop\<guillemotright> e2,h' \<turnstile> (e'' \<guillemotleft>bop\<guillemotright> e2, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(rule bisim1_bisims1.bisim1BinOp1)
    moreover from True have "no_call2 (e1 \<guillemotleft>bop\<guillemotright> e2) pc = no_call2 e1 pc" by(simp add: no_call2_def)
    ultimately show ?thesis using red \<tau>
      by(fastforce intro: Bin1OpRed1 elim!: BinOp_\<tau>red1r_xt1 BinOp_\<tau>red1t_xt1)
  next
    case False
    with pc have pc: "pc = length (compE2 e1)" by auto
    with bisim1 obtain v where e1': "is_val e1' \<longrightarrow> e1' = Val v" 
      and stk: "stk = [v]" and xcp: "xcp = None" and call: "call1 e1' = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len bsok have rede1': "\<tau>red1r P t h (e1', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence rede1'': "\<tau>red1r P t h (e1' \<guillemotleft>bop\<guillemotright> e2, xs) (Val v \<guillemotleft>bop\<guillemotright> e2, loc)" by(rule BinOp_\<tau>red1r_xt1)
    moreover from pc exec stk xcp
    have "exec_meth_d (compP2 P) (compE2 (e1 \<guillemotleft>bop\<guillemotright> e2)) (compxE2 (e1 \<guillemotleft>bop\<guillemotright> e2) 0 0) t h ([] @ [v], loc, length (compE2 e1) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
    hence exec': "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length [v]) (compxE2 e2 0 0)) t h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 e1), xcp')"
      and pc': "pc' \<ge> length (compE2 e1)" by(safe dest!: BinOp_exec2D)simp_all
    then obtain PC' where PC': "pc' = length (compE2 e1) + PC'"
      by -(rule that[where PC'35="pc' - length (compE2 e1)"], simp)
    from exec' bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move_d P t e2 h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 e1), xcp')"
      by(unfold exec_move_def)(drule (1) exec_meth_stk_split, auto)
    with pc xcp have \<tau>: "\<tau>move2 (compP2 P) h [v] (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1)) None = \<tau>move2 (compP2 P) h [] e2 0 None"
      using \<tau>instr_stk_drop_exec_move[where stk="[]" and vs = "[v]"]
      by(simp add: \<tau>move2_iff \<tau>instr_stk_drop_exec_move)
    from bisim1 have "length xs = length loc" by(rule bisim1_length_xs)
    with IH2[OF exec'', of "[]"] len bsok obtain e'' xs''
      where bisim': "P,e2,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 e1), xcp')"
      and red: "?red e2 loc e'' xs'' e2 [] 0 (pc' - length (compE2 e1)) None xcp'" by auto
    from bisim'
    have "P,e1 \<guillemotleft>bop\<guillemotright> e2,h' \<turnstile> (Val v \<guillemotleft>bop\<guillemotright> e'', xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
      by(rule bisim1_bisims1.bisim1BinOp2)
    moreover from red \<tau> 
    have "?red (Val v \<guillemotleft>bop\<guillemotright> e2) loc (Val v \<guillemotleft>bop\<guillemotright> e'') xs'' (e1 \<guillemotleft>bop\<guillemotright> e2) [v] (length (compE2 e1)) pc' None xcp'"
      by(fastforce intro: Bin1OpRed2 elim!: BinOp_\<tau>red1r_xt2 BinOp_\<tau>red1t_xt2 simp add: no_call2_def)
    moreover have "no_call2 (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1))" by(simp add: no_call2_def)
    ultimately show ?thesis using \<tau> stk' pc xcp pc' PC' bisim1 bisim2 e1' stk call by(fastforce elim!: rtranclp_trans)
  qed
next
  case (bisim1BinOp2 e2 n e2' xs stk loc pc xcp e1 bop v1)
  note IH2 = bisim1BinOp2.IH(2)
  note exec = \<open>?exec (e1 \<guillemotleft>bop\<guillemotright> e2) (stk @ [v1]) loc (length (compE2 e1) + pc) xcp stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars (Val v1 \<guillemotleft>bop\<guillemotright> e2') \<le> length xs\<close>
  note bsok = \<open>bsok (e1 \<guillemotleft>bop\<guillemotright> e2) n\<close>
  note ST = \<open>P,h \<turnstile> stk @ [v1] [:\<le>] ST\<close>
  then obtain ST2 T where "ST = ST2 @ [T]" "P,h \<turnstile> stk [:\<le>] ST2" "P,h \<turnstile> v1 :\<le> T"
    by(auto simp add: list_all2_append1 length_Suc_conv)
  from bisim2 have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    with exec have exec': "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) t h (stk @ [v1], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e1), xcp')"
      and pc': "pc' \<ge> length (compE2 e1)"
      by(unfold exec_move_def)(safe dest!: BinOp_exec2D)
    from exec' bisim2 obtain stk'' where stk': "stk' = stk'' @ [v1]"
      and exec'': "exec_move_d P t e2 h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e1), xcp')"
      by -(drule (1) exec_meth_stk_split, auto simp add: exec_move_def)
    with True have \<tau>: "\<tau>move2 (compP2 P) h (stk @ [v1]) (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1) + pc) xcp = \<tau>move2 (compP2 P) h stk e2 pc xcp"
      by(auto simp add: \<tau>move2_iff \<tau>instr_stk_drop_exec_move)
    from IH2[OF exec'' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST2\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain e'' xs''
      where bisim': "P,e2,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 e1), xcp')"
      and red: "?red e2' xs e'' xs'' e2 stk pc (pc' - length (compE2 e1)) xcp xcp'" by auto
    from bisim' have "P,e1 \<guillemotleft>bop\<guillemotright> e2,h' \<turnstile> (Val v1 \<guillemotleft>bop\<guillemotright> e'', xs'') \<leftrightarrow> (stk'' @ [v1], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
      by(rule bisim1_bisims1.bisim1BinOp2)
    with red \<tau> stk' pc' True show ?thesis
      by(fastforce intro: Bin1OpRed2 elim!: BinOp_\<tau>red1r_xt2 BinOp_\<tau>red1t_xt2 split: if_split_asm simp add: no_call2_def)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e2)" by simp
    with bisim2 obtain v2 where e2': "is_val e2' \<longrightarrow> e2' = Val v2" 
      and stk: "stk = [v2]" and xcp: "xcp = None" and call: "call1 e2' = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim2 pc len bsok have red: "\<tau>red1r P t h (e2', xs) (Val v2, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence red1: "\<tau>red1r P t h (Val v1 \<guillemotleft>bop\<guillemotright> e2', xs) (Val v1 \<guillemotleft>bop\<guillemotright> Val v2, loc)" by(rule BinOp_\<tau>red1r_xt2)
    show ?thesis
    proof(cases "the (binop bop v1 v2)")
      case (Inl v)
      note red1
      also from exec xcp ST stk Inl
      have "\<tau>red1r P t h (Val v1 \<guillemotleft>bop\<guillemotright> Val v2, loc) (Val v, loc)"
        by(force simp add: exec_move_def exec_meth_instr list_all2_Cons1 conf_def compP2_def dest: binop_progress intro: r_into_rtranclp Red1BinOp \<tau>move1BinOp)
      also have \<tau>: "\<tau>move2 (compP2 P) h [v2, v1] (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1) + length (compE2 e2)) None"
        by(simp add: \<tau>move2_iff)
      moreover have "P,e1 \<guillemotleft>bop\<guillemotright> e2,h \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (e1 \<guillemotleft>bop\<guillemotright> e2)), None)"
        by(rule bisim1Val2) simp
      ultimately show ?thesis using exec xcp stk call Inl by(auto simp add: exec_move_def exec_meth_instr)
    next
      case (Inr a)
      note red1
      also from exec xcp ST stk Inr
      have "\<tau>red1r P t h (Val v1 \<guillemotleft>bop\<guillemotright> Val v2, loc) (Throw a, loc)"
        by(force simp add: exec_move_def exec_meth_instr list_all2_Cons1 conf_def compP2_def dest: binop_progress intro: r_into_rtranclp Red1BinOpFail \<tau>move1BinOp)
      also have \<tau>: "\<tau>move2 (compP2 P) h [v2, v1] (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1) + length (compE2 e2)) None"
        by(simp add: \<tau>move2_iff)
      moreover
      have "P,e1 \<guillemotleft>bop\<guillemotright> e2,h \<turnstile> (Throw a, loc) \<leftrightarrow> ([v2, v1], loc, length (compE2 e1) + length (compE2 e2), \<lfloor>a\<rfloor>)"
        by(rule bisim1BinOpThrow)
      ultimately show ?thesis using exec xcp stk call Inr by(auto simp add: exec_move_def exec_meth_instr)
    qed
  qed
next
  case (bisim1BinOpThrow1 e1 n a xs stk loc pc e2 bop)
  note exec = \<open>?exec (e1 \<guillemotleft>bop\<guillemotright> e2) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim1 have pc: "pc < length (compE2 e1)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e1 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False by(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
  thus ?case ..
next
  case (bisim1BinOpThrow2 e2 n a xs stk loc pc e1 bop v1)
  note exec = \<open>?exec (e1 \<guillemotleft>bop\<guillemotright> e2) (stk @ [v1]) loc (length (compE2 e1) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  hence "match_ex_table (compP2 P) (cname_of h a) (length (compE2 e1) + pc) (compxE2 e2 (length (compE2 e1)) 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec have False
    apply(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs exec_move_def)
    apply(auto simp only: compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_stack_xlift_eq_Some_conv)
    done
  thus ?case ..
next 
  case (bisim1BinOpThrow e1 n e2 bop a xs v1 v2)
  note \<open>?exec (e1 \<guillemotleft>bop\<guillemotright> e2) [v1, v2] xs (length (compE2 e1) + length (compE2 e2)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  hence False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs compxE2_size_convs exec_move_def
               dest!: match_ex_table_shift_pcD match_ex_table_pc_length_compE2)
  thus ?case ..
next
  case (bisim1LAss1 e n e' xs stk loc pc xcp V)
  note IH = bisim1LAss1.IH(2)
  note exec = \<open>?exec (V := e) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars (V := e') \<le> length xs\<close>
  note bsok = \<open>bsok (V:=e) n\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'" by(auto simp add: exec_move_LAss)
    from True have "\<tau>move2 (compP2 P) h stk (V := e) pc xcp = \<tau>move2 (compP2 P) h stk e pc xcp" by(simp add: \<tau>move2_iff)
    with IH[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok show ?thesis
      by(fastforce intro: bisim1_bisims1.bisim1LAss1 LAss1Red elim!: LAss_\<tau>red1r LAss_\<tau>red1t simp add: no_call2_def)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (V := e', xs) (V := Val v, loc)" by(rule LAss_\<tau>red1r)
    also have "\<tau>move1 P h (V := Val v)" by(rule \<tau>move1LAssRed)
    with exec stk xcp have "\<tau>red1r P t h (V := Val v, loc) (unit, loc[V := v])"
      by(auto intro!: r_into_rtranclp Red1LAss simp add: exec_move_def elim!: exec_meth.cases)
    also have \<tau>: "\<tau>move2 (compP2 P) h [v] (V := e) pc None" by(simp add: \<tau>move2_iff)
    moreover have "P,(V := e),h \<turnstile> (unit, loc[V := v]) \<leftrightarrow> ([], loc[V := v], Suc (length (compE2 e)), None)"
      by(rule bisim1LAss2)
    ultimately show ?thesis using exec stk xcp
      by(fastforce elim!: exec_meth.cases simp add: exec_move_def)
  qed
next
  case (bisim1LAss2 e n V xs)
  note bisim = \<open>P,e,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note exec = \<open>?exec (V := e) [] xs (Suc (length (compE2 e))) None stk' loc' pc' xcp'\<close>
  hence "stk' = [Unit]" "loc' = xs" "pc' = length (compE2 (V := e))" "xcp' = None" "h' = h"
    by(auto elim!: exec_meth.cases simp add: exec_move_def)
  moreover have "\<tau>move2 (compP2 P) h [] (V := e) (Suc (length (compE2 e))) None" by(simp add: \<tau>move2_iff)
  moreover have "P,V:=e,h' \<turnstile> (unit, xs) \<leftrightarrow> ([Unit], xs, length (compE2 (V := e)), None)"
    by(rule bisim1Val2) simp
  ultimately show ?case by(auto)
next
  case (bisim1LAssThrow e n a xs stk loc pc V)
  note exec = \<open>?exec (V := e) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False by (auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1AAcc1 a n a' xs stk loc pc xcp i)
  note IH1 = bisim1AAcc1.IH(2)
  note IH2 = bisim1AAcc1.IH(4)
  note exec = \<open>?exec (a\<lfloor>i\<rceil>) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,a,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note len = \<open>n + max_vars (a'\<lfloor>i\<rceil>) \<le> length xs\<close>
  note bsok = \<open>bsok (a\<lfloor>i\<rceil>) n\<close>
  from bisim1 have pc: "pc \<le> length (compE2 a)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 a)")
    case True
    with exec have exec': "?exec a stk loc pc xcp stk' loc' pc' xcp'" by(auto simp add: exec_move_AAcc1)
    from True have \<tau>: "\<tau>move2 (compP2 P) h stk (a\<lfloor>i\<rceil>) pc xcp = \<tau>move2 (compP2 P) h stk a pc xcp" by(auto intro: \<tau>move2AAcc1)
    with IH1[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain e'' xs''
      where bisim': "P,a,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red a' xs e'' xs'' a stk pc pc' xcp xcp'" by auto
    from bisim' have "P,a\<lfloor>i\<rceil>,h' \<turnstile> (e''\<lfloor>i\<rceil>, xs'') \<leftrightarrow> (stk', loc', pc', xcp')" by(rule bisim1_bisims1.bisim1AAcc1)
    moreover from True have "no_call2 (a\<lfloor>i\<rceil>) pc = no_call2 a pc" by(simp add: no_call2_def)
    ultimately show ?thesis using red \<tau> by(fastforce intro: AAcc1Red1 elim!: AAcc_\<tau>red1r_xt1 AAcc_\<tau>red1t_xt1)
  next
    case False
    with pc have pc: "pc = length (compE2 a)" by auto
    with bisim1 obtain v where a': "is_val a' \<longrightarrow> a' = Val v" 
      and stk: "stk = [v]" and xcp: "xcp = None" and call: "call1 a' = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len bsok have rede1': "\<tau>red1r P t h (a', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (a'\<lfloor>i\<rceil>, xs) (Val v\<lfloor>i\<rceil>, loc)" by(rule AAcc_\<tau>red1r_xt1)
    moreover from pc exec stk xcp
    have exec': "exec_meth_d (compP2 P) (compE2 a @ compE2 i @ [ALoad]) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0))) t h ([] @ [v], loc, length (compE2 a) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
    hence "exec_meth_d (compP2 P) (compE2 i @ [ALoad]) (stack_xlift (length [v]) (compxE2 i 0 0)) t h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth_d (compP2 P) (compE2 i) (stack_xlift (length [v]) (compxE2 i 0 0)) t h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_take) simp
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move_d P t i h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 a), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    with pc xcp have \<tau>: "\<tau>move2 (compP2 P) h ([] @ [v]) (a\<lfloor>i\<rceil>) (length (compE2 a)) None = \<tau>move2 (compP2 P) h [] i 0 None"
      using \<tau>instr_stk_drop_exec_move[where stk="[]" and vs="[v]"]
      by(auto simp add: \<tau>move2_iff \<tau>instr_stk_drop_exec_move)
    from bisim1 have "length xs = length loc" by(rule bisim1_length_xs)
    with IH2[OF exec''] len bsok obtain e'' xs''
      where bisim': "P,i,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a), xcp')"
      and red: "?red i loc e'' xs'' i [] 0 (pc' - length (compE2 a)) None xcp'" by(fastforce)
    from bisim'
    have "P,a\<lfloor>i\<rceil>,h' \<turnstile> (Val v\<lfloor>e''\<rceil>, xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule bisim1_bisims1.bisim1AAcc2)
    moreover from red \<tau> have "?red (Val v\<lfloor>i\<rceil>) loc (Val v\<lfloor>e''\<rceil>) xs'' (a\<lfloor>i\<rceil>) [v] (length (compE2 a)) pc' None xcp'"
      by(fastforce intro: AAcc1Red2 elim!: AAcc_\<tau>red1r_xt2 AAcc_\<tau>red1t_xt2 split: if_split_asm simp add: no_call2_def)
    moreover from exec' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc) auto
    moreover have "no_call2 (a\<lfloor>i\<rceil>) pc" using pc by(simp add: no_call2_def)
    ultimately show ?thesis using \<tau> stk' pc xcp stk call
      by(fastforce elim!: rtranclp_trans)+
  qed
next
  case (bisim1AAcc2 i n i' xs stk loc pc xcp a v)
  note IH2 = bisim1AAcc2.IH(2)
  note exec = \<open>?exec (a\<lfloor>i\<rceil>) (stk @ [v]) loc (length (compE2 a) + pc) xcp stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars (Val v\<lfloor>i'\<rceil>) \<le> length xs\<close>
  note bsok = \<open>bsok (a\<lfloor>i\<rceil>) n\<close>
  from bisim2 have pc: "pc \<le> length (compE2 i)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 i)")
    case True
    from exec have exec': "exec_meth_d (compP2 P) (compE2 a @ compE2 i @ [ALoad]) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0))) t h (stk @ [v], loc, length (compE2 a) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2 exec_move_def)
    hence "exec_meth_d (compP2 P) (compE2 i @ [ALoad]) (stack_xlift (length [v]) (compxE2 i 0 0)) t h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth_d (compP2 P) (compE2 i) (stack_xlift (length [v]) (compxE2 i 0 0)) t h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      using True by(rule exec_meth_take)
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move_d P t i h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    with True have \<tau>: "\<tau>move2 (compP2 P) h (stk @ [v]) (a\<lfloor>i\<rceil>) (length (compE2 a) + pc) xcp = \<tau>move2 (compP2 P) h stk i pc xcp"
      by(auto simp add: \<tau>move2_iff \<tau>instr_stk_drop_exec_move)
    moreover from \<open>P,h \<turnstile> stk @ [v] [:\<le>] ST\<close> obtain ST2
      where "P,h \<turnstile> stk [:\<le>] ST2" by(auto simp add: list_all2_append1)
    from IH2[OF exec'' _ _ this \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain e'' xs''
      where bisim': "P,i,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a), xcp')"
      and red: "?red i' xs e'' xs'' i stk pc (pc' - length (compE2 a)) xcp xcp'" by auto
    from bisim' have "P,a\<lfloor>i\<rceil>,h' \<turnstile> (Val v\<lfloor>e''\<rceil>, xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule bisim1_bisims1.bisim1AAcc2)
    moreover from exec' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc) auto
    moreover have "no_call2 i pc \<Longrightarrow> no_call2 (a\<lfloor>i\<rceil>) (length (compE2 a) + pc)"
      by(simp add: no_call2_def)
    ultimately show ?thesis using red \<tau> stk' True
      by(fastforce intro: AAcc1Red2 elim!: AAcc_\<tau>red1r_xt2 AAcc_\<tau>red1t_xt2 split: if_split_asm)
  next
    case False
    with pc have [simp]: "pc = length (compE2 i)" by simp
    with bisim2 obtain v2 where i': "is_val i' \<longrightarrow> i' = Val v2" 
      and stk: "stk = [v2]" and xcp: "xcp = None" and call: "call1 i' = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim2 pc len bsok have red: "\<tau>red1r P t h (i', xs) (Val v2, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (Val v\<lfloor>i'\<rceil>, xs) (Val v\<lfloor>Val v2\<rceil>, loc)" by(rule AAcc_\<tau>red1r_xt2)
    moreover have \<tau>: "\<not> \<tau>move2 (compP2 P) h [v2, v] (a\<lfloor>i\<rceil>) (length (compE2 a) + length (compE2 i)) None"
      by(simp add: \<tau>move2_iff)
    moreover 
    have "\<exists>ta' e''. P,a\<lfloor>i\<rceil>,h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> True,P,t \<turnstile>1 \<langle>Val v\<lfloor>Val v2\<rceil>, (h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim wbisim1 (extTA2J1 P ta') ta"
    proof(cases "v = Null")
      case True with exec stk xcp show ?thesis
        by(fastforce elim!: exec_meth.cases simp add: exec_move_def intro: bisim1AAccFail Red1AAccNull)
    next
      case False
      with exec xcp stk obtain U el A len I where [simp]: "v = Addr A" and hA: "typeof_addr h A = \<lfloor>Array_type U len\<rfloor>"
        and [simp]: "v2 = Intg I" by(auto simp add: exec_move_def exec_meth_instr is_Ref_def conf_def split: if_split_asm)
      show ?thesis
      proof(cases "0 <=s I \<and> sint I < int len")
        case True
        hence "\<not> I <s 0" by auto
        moreover
        with exec xcp stk True hA obtain v3 where "stk' = [v3]" "heap_read h A (ACell (nat (sint I))) v3"
          by(auto simp add: exec_move_def exec_meth_instr is_Ref_def)
        moreover        
        have "P,a\<lfloor>i\<rceil>,h' \<turnstile> (Val v3,loc) \<leftrightarrow> ([v3], loc, length (compE2 (a\<lfloor>i\<rceil>)), None)"
          by(rule bisim1Val2) simp
        ultimately show ?thesis using exec stk xcp True hA
          by(fastforce elim!: exec_meth.cases intro: Red1AAcc simp add: exec_move_def ta_upd_simps ta_bisim_def split: if_split_asm)
      next
        case False
        with exec stk xcp hA show ?thesis
          by(fastforce elim!: exec_meth.cases simp add: is_Ref_def exec_move_def intro: bisim1AAccFail Red1AAccBounds split: if_split_asm)
      qed
    qed
    ultimately show ?thesis using exec xcp stk call by fastforce
  qed
next
  case (bisim1AAccThrow1 A n a xs stk loc pc i)
  note exec = \<open>?exec (A\<lfloor>i\<rceil>) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,A,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim1 have pc: "pc < length (compE2 A)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 A 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
  thus ?case ..
next
  case (bisim1AAccThrow2 i n a xs stk loc pc A v)
  note exec = \<open>?exec (A\<lfloor>i\<rceil>) (stk @ [v]) loc (length (compE2 A) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  hence "match_ex_table (compP2 P) (cname_of h a) (length (compE2 A) + pc) (compxE2 i (length (compE2 A)) 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec have False
    apply(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs exec_move_def)
    apply(auto simp only: compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_stack_xlift_eq_Some_conv)
    done
  thus ?case ..
next
  case (bisim1AAccFail a n i ad xs v v')
  note \<open>?exec (a\<lfloor>i\<rceil>) [v, v'] xs (length (compE2 a) + length (compE2 i)) \<lfloor>ad\<rfloor> stk' loc' pc' xcp'\<close>
  hence False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs compxE2_size_convs exec_move_def
               dest!: match_ex_table_shift_pcD match_ex_table_pc_length_compE2)
  thus ?case ..
next
  case (bisim1AAss1 a n a' xs stk loc pc xcp i e)
  note IH1 = bisim1AAss1.IH(2)
  note IH2 = bisim1AAss1.IH(4)
  note exec = \<open>?exec (a\<lfloor>i\<rceil> := e) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,a,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note len = \<open>n + max_vars (a'\<lfloor>i\<rceil> := e) \<le> length xs\<close>
  note bsok = \<open>bsok (a\<lfloor>i\<rceil> := e) n\<close>
  from bisim1 have pc: "pc \<le> length (compE2 a)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 a)")
    case True
    with exec have exec': "?exec a stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_AAss1)
    from True have \<tau>: "\<tau>move2 (compP2 P) h stk (a\<lfloor>i\<rceil> := e) pc xcp = \<tau>move2 (compP2 P) h stk a pc xcp" by(simp add: \<tau>move2_iff)
    with IH1[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain e'' xs''
      where bisim': "P,a,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red a' xs e'' xs'' a stk pc pc' xcp xcp'" by auto
    from bisim' have "P,a\<lfloor>i\<rceil> := e,h' \<turnstile> (e''\<lfloor>i\<rceil> := e, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(rule bisim1_bisims1.bisim1AAss1)
    moreover from True have "no_call2 (a\<lfloor>i\<rceil> := e) pc = no_call2 a pc" by(simp add: no_call2_def)
    ultimately show ?thesis using red \<tau> by(fastforce intro: AAss1Red1 elim!: AAss_\<tau>red1r_xt1 AAss_\<tau>red1t_xt1)
  next
    case False
    with pc have pc: "pc = length (compE2 a)" by auto
    with bisim1 obtain v where a': "is_val a' \<longrightarrow> a' = Val v" 
      and stk: "stk = [v]" and xcp: "xcp = None" and call: "call1 a' = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len bsok have rede1': "\<tau>red1r P t h (a', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (a'\<lfloor>i\<rceil> := e, xs) (Val v\<lfloor>i\<rceil> := e, loc)" by(rule AAss_\<tau>red1r_xt1)
    moreover from pc exec stk xcp
    have exec': "exec_meth_d (compP2 P) (compE2 a @ compE2 i @ compE2 e @ [AStore, Push Unit]) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0) @ shift (length (compE2 i)) (compxE2 e 0 (Suc (Suc 0))))) t h ([] @ [v], loc, length (compE2 a) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
    hence "exec_meth_d (compP2 P) (compE2 i @ compE2 e @ [AStore, Push Unit]) (stack_xlift (length [v]) (compxE2 i 0 0) @ shift (length (compE2 i)) (compxE2 e 0 (Suc (Suc 0)))) t h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth_d (compP2 P) (compE2 i) (stack_xlift (length [v]) (compxE2 i 0 0)) t h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_take_xt) simp
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move_d P t i h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 a), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    with pc xcp have \<tau>: "\<tau>move2 (compP2 P) h [v] (a\<lfloor>i\<rceil>:= e) (length (compE2 a)) None = \<tau>move2 (compP2 P) h [] i 0 None"
      using \<tau>instr_stk_drop_exec_move[where stk="[]" and vs="[v]"]
      by(auto simp add: \<tau>move2_iff)
    from bisim1 have "length xs = length loc" by(rule bisim1_length_xs)
    with IH2[OF exec''] len bsok obtain e'' xs''
      where bisim': "P,i,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a), xcp')"
      and red: "?red i loc e'' xs'' i [] 0 (pc' - length (compE2 a)) None xcp'" by fastforce
    from bisim'
    have "P,a\<lfloor>i\<rceil> := e,h' \<turnstile> (Val v\<lfloor>e''\<rceil> := e, xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule bisim1_bisims1.bisim1AAss2)
    moreover from red \<tau> have "?red (Val v\<lfloor>i\<rceil> := e) loc (Val v\<lfloor>e''\<rceil> := e) xs'' (a\<lfloor>i\<rceil> := e) [v] (length (compE2 a)) pc' None xcp'"
      by(fastforce intro: AAss1Red2 elim!: AAss_\<tau>red1r_xt2 AAss_\<tau>red1t_xt2 split: if_split_asm simp add: no_call2_def)
    moreover from exec' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc) auto
    moreover have "no_call2 (a\<lfloor>i\<rceil> := e) pc" using pc by(simp add: no_call2_def)
    ultimately show ?thesis using \<tau> stk' pc xcp stk by(fastforce elim!: rtranclp_trans)
  qed
next
  case (bisim1AAss2 i n i' xs stk loc pc xcp a e v)
  note IH2 = bisim1AAss2.IH(2)
  note IH3 = bisim1AAss2.IH(6)
  note exec = \<open>?exec (a\<lfloor>i\<rceil> := e) (stk @ [v]) loc (length (compE2 a) + pc) xcp stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim3 = \<open>P,e,h \<turnstile> (e, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note len = \<open>n + max_vars (Val v\<lfloor>i'\<rceil> := e) \<le> length xs\<close>
  note bsok = \<open>bsok (a\<lfloor>i\<rceil> := e) n\<close>
  from bisim2 have pc: "pc \<le> length (compE2 i)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 i)")
    case True
    from exec have exec': "exec_meth_d (compP2 P) (compE2 a @ compE2 i @ compE2 e @ [AStore, Push Unit]) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0) @ shift (length (compE2 i)) (compxE2 e 0 (Suc (Suc 0))))) t h (stk @ [v], loc, length (compE2 a) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2 ac_simps exec_move_def)
    hence "exec_meth_d (compP2 P) (compE2 i @ compE2 e @ [AStore, Push Unit]) (stack_xlift (length [v]) (compxE2 i 0 0) @ shift (length (compE2 i)) (compxE2 e 0 (Suc (Suc 0)))) t h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth_d (compP2 P) (compE2 i) (stack_xlift (length [v]) (compxE2 i 0 0)) t h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      using True by(rule exec_meth_take_xt)
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move_d P t i h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    with True have \<tau>: "\<tau>move2 (compP2 P) h (stk @ [v]) (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc) xcp = \<tau>move2 (compP2 P) h stk i pc xcp"
      by(auto simp add: \<tau>move2_iff \<tau>instr_stk_drop_exec_move)
    moreover from \<open>P,h \<turnstile> stk @ [v] [:\<le>] ST\<close> obtain ST2 where "P,h \<turnstile> stk [:\<le>] ST2" by(auto simp add: list_all2_append1)
    from IH2[OF exec'' _ _ this \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain e'' xs''
      where bisim': "P,i,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a), xcp')"
      and red: "?red i' xs e'' xs'' i stk pc (pc' - length (compE2 a)) xcp xcp'" by fastforce
    from bisim'
    have "P,a\<lfloor>i\<rceil> := e,h' \<turnstile> (Val v\<lfloor>e''\<rceil> := e, xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule bisim1_bisims1.bisim1AAss2)
    moreover from exec' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc) auto
    moreover have "no_call2 i pc \<Longrightarrow> no_call2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc)" by(simp add: no_call2_def)
    ultimately show ?thesis using red \<tau> stk' True
      by(fastforce intro: AAss1Red2 elim!: AAss_\<tau>red1r_xt2 AAss_\<tau>red1t_xt2 split: if_split_asm)
  next
    case False
    with pc have [simp]: "pc = length (compE2 i)" by simp
    with bisim2 obtain v2 where i': "is_val i' \<longrightarrow> i' = Val v2" 
      and stk: "stk = [v2]" and xcp: "xcp = None" and call: "call1 i' = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim2 pc len bsok have red: "\<tau>red1r P t h (i', xs) (Val v2, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (Val v\<lfloor>i'\<rceil> := e, xs) (Val v\<lfloor>Val v2\<rceil> := e, loc)" by(rule AAss_\<tau>red1r_xt2)
    moreover from pc exec stk xcp
    have exec': "exec_meth_d (compP2 P) ((compE2 a @ compE2 i) @ compE2 e @ [AStore, Push Unit]) ((compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0)) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length [v2, v]) (compxE2 e 0 0))) t h ([] @ [v2, v], loc, length (compE2 a @ compE2 i) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
    hence "exec_meth_d (compP2 P) (compE2 e @ [AStore, Push Unit]) (stack_xlift (length [v2, v]) (compxE2 e 0 0)) t h ([] @ [v2, v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth_d (compP2 P) (compE2 e) (stack_xlift (length [v2, v]) (compxE2 e 0 0)) t h ([] @ [v2, v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      by(rule exec_meth_take) simp
    with bisim3 obtain stk'' where stk': "stk' = stk'' @ [v2, v]"
      and exec'': "exec_move_d P t e h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    with pc xcp have \<tau>: "\<tau>move2 (compP2 P) h [v2, v] (a\<lfloor>i\<rceil>:= e) (length (compE2 a) + length (compE2 i)) None = \<tau>move2 (compP2 P) h [] e 0 None"
      using \<tau>instr_stk_drop_exec_move[where stk="[]" and vs="[v2, v]"] by(simp add: \<tau>move2_iff)
    from bisim2 have "length xs = length loc" by(rule bisim1_length_xs)
    with IH3[OF exec'', of "[]"] len bsok obtain e'' xs''
      where bisim': "P,e,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a) - length (compE2 i), xcp')"
      and red: "?red e loc e'' xs'' e [] 0 (pc' - length (compE2 a) - length (compE2 i)) None xcp'"
      by auto (fastforce simp only: length_append diff_diff_left)
    from bisim'
    have "P,a\<lfloor>i\<rceil> := e,h' \<turnstile> (Val v\<lfloor>Val v2\<rceil> := e'', xs'') \<leftrightarrow> (stk'' @ [v2, v], loc', length (compE2 a) + length (compE2 i) + (pc' - length (compE2 a) - length (compE2 i)), xcp')"
      by(rule bisim1_bisims1.bisim1AAss3)
    moreover from red \<tau>
    have "?red (Val v\<lfloor>Val v2\<rceil> := e) loc (Val v\<lfloor>Val v2\<rceil> := e'') xs'' (a\<lfloor>i\<rceil> := e) [v2, v] (length (compE2 a) + length (compE2 i)) pc' None xcp'"
      by(fastforce intro: AAss1Red3 elim!: AAss_\<tau>red1r_xt3 AAss_\<tau>red1t_xt3 split: if_split_asm simp add: no_call2_def)
    moreover from exec' have "pc' \<ge> length (compE2 a @ compE2 i)"
      by(rule exec_meth_drop_xt_pc) auto
    moreover have "no_call2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc)" by(simp add: no_call2_def)
    ultimately show ?thesis using \<tau> stk' pc xcp stk by(fastforce elim!: rtranclp_trans)
  qed
next
  case (bisim1AAss3 e n e' xs stk loc pc xcp a i v v')
  note IH3 = bisim1AAss3.IH(2)
  note exec = \<open>?exec (a\<lfloor>i\<rceil> := e) (stk @ [v', v]) loc (length (compE2 a) + length (compE2 i) + pc) xcp stk' loc' pc' xcp'\<close>
  note bisim3 = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars (Val v\<lfloor>Val v'\<rceil> := e') \<le> length xs\<close>
  note bsok = \<open>bsok (a\<lfloor>i\<rceil> := e) n\<close>
  from \<open>P,h \<turnstile> stk @ [v', v] [:\<le>] ST\<close> obtain T T' ST'
    where [simp]: "ST = ST' @ [T', T]"
    and wtv: "P,h \<turnstile> v :\<le> T" and wtv': "P,h \<turnstile> v' :\<le> T'" and ST': "P,h \<turnstile> stk [:\<le>] ST'"
    by(auto simp add: list_all2_Cons1 list_all2_append1)
  from bisim3 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    from exec have exec': "exec_meth_d (compP2 P) ((compE2 a @ compE2 i) @ compE2 e @ [AStore, Push Unit]) ((compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0)) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length [v', v]) (compxE2 e 0 0))) t h (stk @ [v', v], loc, length (compE2 a @ compE2 i) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2 exec_move_def)
    hence "exec_meth_d (compP2 P) (compE2 e @ [AStore, Push Unit]) (stack_xlift (length [v', v]) (compxE2 e 0 0)) t h (stk @ [v', v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth_d (compP2 P) (compE2 e) (stack_xlift (length [v', v]) (compxE2 e 0 0)) t h (stk @ [v', v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      using True by(rule exec_meth_take)
    with bisim3 obtain stk'' where stk': "stk' = stk'' @ [v', v]"
      and exec'': "exec_move_d P t e h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    with True have \<tau>: "\<tau>move2 (compP2 P) h (stk @ [v', v]) (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + pc) xcp = \<tau>move2 (compP2 P) h stk e pc xcp"
      by(auto simp add: \<tau>move2_iff \<tau>instr_stk_drop_exec_move)
    moreover from IH3[OF exec'' _ _ ST' \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain e'' xs''
      where bisim': "P,e,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a) - length (compE2 i), xcp')"
      and red: "?red e' xs e'' xs'' e stk pc (pc' - length (compE2 a) - length (compE2 i)) xcp xcp'"
      by auto(fastforce simp only: length_append diff_diff_left)
    from bisim'
    have "P,a\<lfloor>i\<rceil> := e,h' \<turnstile> (Val v\<lfloor>Val v'\<rceil> := e'', xs'') \<leftrightarrow> (stk'' @ [v', v], loc', length (compE2 a) + length (compE2 i) + (pc' - length (compE2 a) - length (compE2 i)), xcp')"
      by(rule bisim1_bisims1.bisim1AAss3)
    moreover from exec' have "pc' \<ge> length (compE2 a @ compE2 i)"
      by(rule exec_meth_drop_xt_pc) auto
    moreover have "no_call2 e pc \<Longrightarrow> no_call2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + pc)"
      by(simp add: no_call2_def)
    ultimately show ?thesis using red \<tau> stk' True
      by(fastforce intro: AAss1Red3 elim!: AAss_\<tau>red1r_xt3 AAss_\<tau>red1t_xt3 split: if_split_asm)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim3 obtain v2 where stk: "stk = [v2]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim3 pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v2, loc)" 
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (Val v\<lfloor>Val v'\<rceil> := e', xs) (Val v\<lfloor>Val v'\<rceil> := Val v2, loc)" by(rule AAss_\<tau>red1r_xt3)
    moreover have \<tau>: "\<not> \<tau>move2 (compP2 P) h [v2, v', v] (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None"
      by(simp add: \<tau>move2_iff)
    moreover 
    have "\<exists>ta' e''. P,a\<lfloor>i\<rceil> := e,h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> True,P,t \<turnstile>1 \<langle>Val v\<lfloor>Val v'\<rceil> := Val v2, (h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim wbisim1 (extTA2J1 P ta') ta"
    proof(cases "v = Null")
      case True with exec stk xcp show ?thesis
        by(fastforce elim!: exec_meth.cases simp add: exec_move_def intro: bisim1AAssFail Red1AAssNull)
    next
      case False
      with exec stk xcp  obtain U A len I where [simp]: "v = Addr A" "v' = Intg I"
        and hA: "typeof_addr h A = \<lfloor>Array_type U len\<rfloor>"
        by(fastforce simp add: exec_move_def exec_meth_instr is_Ref_def)
      from ST' stk obtain T3 where wt3': "typeof\<^bsub>h\<^esub> v2 = \<lfloor>T3\<rfloor>" by(auto simp add: list_all2_Cons1 conf_def)
      show ?thesis
      proof(cases "0 <=s I \<and> sint I < int len")
        case True
        note I = True
        show ?thesis
        proof(cases "P \<turnstile> T3 \<le> U")
          case True
          with exec stk xcp True hA I wt3' show ?thesis
            by(fastforce elim!: exec_meth.cases simp add: compP2_def exec_move_def ta_bisim_def ta_upd_simps intro: Red1AAss bisim1AAss4 split: if_split_asm)
        next
          case False
          with exec stk xcp True hA I wt3' show ?thesis
            by(fastforce elim!: exec_meth.cases simp add: compP2_def exec_move_def intro: Red1AAssStore bisim1AAssFail split: if_split_asm)
        qed
      next
        case False
        with exec stk xcp hA show ?thesis
          by(fastforce elim!: exec_meth.cases intro: bisim1AAssFail Red1AAssBounds simp add: exec_move_def split: if_split_asm)
      qed
    qed
    ultimately show ?thesis using exec xcp stk by(fastforce simp add: no_call2_def)
  qed
next
  case (bisim1AAssThrow1 A n a xs stk loc pc i e)
  note exec = \<open>?exec (A\<lfloor>i\<rceil> := e) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,A,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim1 have pc: "pc < length (compE2 A)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 A 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
  thus ?case ..
next
  case (bisim1AAssThrow2 i n a xs stk loc pc A e v)
  note exec = \<open>?exec (A\<lfloor>i\<rceil> := e) (stk @ [v]) loc (length (compE2 A) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim2 have pc: "pc < length (compE2 i)" by(auto dest: bisim1_ThrowD)
  from bisim2 have "match_ex_table (compP2 P) (cname_of h a) (length (compE2 A) + pc) (compxE2 i (length (compE2 A)) 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False
    apply(auto elim!: exec_meth.cases simp add: compxE2_stack_xlift_convs compxE2_size_convs exec_move_def)
    apply(auto simp add: match_ex_table_append_not_pcs)
    done
  thus ?case .. 
next
  case (bisim1AAssThrow3 e n a xs stk loc pc A i v' v)
  note exec = \<open>?exec (A\<lfloor>i\<rceil> := e) (stk @ [v', v]) loc (length (compE2 A) + length (compE2 i) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim2 have "match_ex_table (compP2 P) (cname_of h a) (length (compE2 A) + length (compE2 i) + pc) (compxE2 e (length (compE2 A) + length (compE2 i)) 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec have False
    apply(auto elim!: exec_meth.cases simp add: compxE2_stack_xlift_convs compxE2_size_convs exec_move_def)
    apply(auto dest!: match_ex_table_stack_xliftD match_ex_table_shift_pcD dest: match_ex_table_pcsD simp add: match_ex_table_append match_ex_table_shift_pc_None)
    done
  thus ?case .. 
next
  case (bisim1AAssFail a n i e ad xs v' v v'')
  note exec = \<open>?exec (a\<lfloor>i\<rceil> := e) [v', v, v''] xs (length (compE2 a) + length (compE2 i) + length (compE2 e)) \<lfloor>ad\<rfloor> stk' loc' pc' xcp'\<close>
  hence False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_append exec_move_def
            dest!: match_ex_table_shift_pcD match_ex_table_pc_length_compE2)
  thus ?case ..
next
  case (bisim1AAss4 a n i e xs)
  have "P,a\<lfloor>i\<rceil> := e,h \<turnstile> (unit, xs) \<leftrightarrow> ([Unit], xs, length (compE2 (a\<lfloor>i\<rceil> := e)), None)" by(rule bisim1Val2) simp
  moreover have "\<tau>move2 (compP2 P) h [] (a\<lfloor>i\<rceil> := e) (Suc (length (compE2 a) + length (compE2 i) + length (compE2 e))) None"
    by(simp add: \<tau>move2_iff)
  moreover note \<open>?exec (a\<lfloor>i\<rceil> := e) [] xs (Suc (length (compE2 a) + length (compE2 i) + length (compE2 e))) None stk' loc' pc' xcp'\<close>
  ultimately show ?case
    by(fastforce elim!: exec_meth.cases simp add: ac_simps exec_move_def)
next
  case (bisim1ALength a n a' xs stk loc pc xcp)
  note IH = bisim1ALength.IH(2)
  note exec = \<open>?exec (a\<bullet>length) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,a,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars (a'\<bullet>length) \<le> length xs\<close>
  note bsok = \<open>bsok (a\<bullet>length) n\<close>
  from bisim have pc: "pc \<le> length (compE2 a)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 a)")
    case True
    with exec have exec': "?exec a stk loc pc xcp stk' loc' pc' xcp'" by(auto simp add: exec_move_ALength)
    from True have \<tau>: "\<tau>move2 (compP2 P) h stk (a\<bullet>length) pc xcp = \<tau>move2 (compP2 P) h stk a pc xcp" by(simp add: \<tau>move2_iff)
    with IH[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain e'' xs''
      where bisim': "P,a,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red a' xs e'' xs'' a stk pc pc' xcp xcp'" by auto
    from bisim' have "P,a\<bullet>length,h' \<turnstile> (e''\<bullet>length, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(rule bisim1_bisims1.bisim1ALength)
    with red \<tau> show ?thesis by(fastforce intro: ALength1Red elim!: ALength_\<tau>red1r_xt ALength_\<tau>red1t_xt simp add: no_call2_def)
  next
    case False
    with pc have pc: "pc = length (compE2 a)" by auto
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len bsok have "\<tau>red1r P t h (a', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (a'\<bullet>length, xs) (Val v\<bullet>length, loc)" by(rule ALength_\<tau>red1r_xt)
    moreover
    moreover have \<tau>: "\<not> \<tau>move2 (compP2 P) h [v] (a\<bullet>length) (length (compE2 a)) None" by(simp add: \<tau>move2_iff)
    moreover have "\<exists>ta' e''. P,a\<bullet>length,h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> True,P,t \<turnstile>1 \<langle>Val v\<bullet>length, (h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim wbisim1 (extTA2J1 P ta') ta"
    proof(cases "v = Null")
      case True with exec stk xcp pc show ?thesis
        by(fastforce elim!: exec_meth.cases simp add: exec_move_def intro: bisim1ALengthNull Red1ALengthNull)
    next
      case False
      with exec stk xcp pc \<open>P,h \<turnstile> stk [:\<le>] ST\<close>
      obtain U A len where [simp]: "v = Addr A"
        and hA: "typeof_addr h A = \<lfloor>Array_type U len\<rfloor>"
        by(fastforce simp add: exec_move_def exec_meth_instr is_Ref_def list_all2_Cons1)
      have "P,a\<bullet>length,h' \<turnstile> (Val (Intg (word_of_int (int len))),loc) \<leftrightarrow> ([Intg (word_of_int (int len))], loc, length (compE2 (a\<bullet>length)), None)"
        by(rule bisim1Val2) simp
      thus ?thesis using exec stk xcp hA pc
        by(fastforce elim!: exec_meth.cases intro: Red1ALength simp add: exec_move_def)
    qed
    ultimately show ?thesis using \<tau> pc xcp stk by(fastforce elim!: rtranclp_trans simp add: no_call2_def)
  qed
next
  case (bisim1ALengthThrow A n a xs stk loc pc)
  note exec = \<open>?exec (A\<bullet>length) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,A,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim1 have pc: "pc < length (compE2 A)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 A 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False by(auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1ALengthNull a n xs)
  note exec = \<open>?exec (a\<bullet>length) [Null] xs (length (compE2 a)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'\<close>
  hence False by(auto elim!: exec_meth.cases dest!: match_ex_table_pc_length_compE2 simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1FAcc e n e' xs stk loc pc xcp F D)
  note IH = bisim1FAcc.IH(2)
  note exec = \<open>?exec (e\<bullet>F{D}) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars (e'\<bullet>F{D}) \<le> length xs\<close>
  note bsok = \<open>bsok (e\<bullet>F{D}) n\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_FAcc)
    from True have \<tau>: "\<tau>move2 (compP2 P) h stk (e\<bullet>F{D}) pc xcp = \<tau>move2 (compP2 P) h stk e pc xcp" by(simp add: \<tau>move2_iff)
    with IH[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain e'' xs''
      where bisim': "P,e,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red e' xs e'' xs'' e stk pc pc' xcp xcp'" by auto
    from bisim' have "P,e\<bullet>F{D},h' \<turnstile> (e''\<bullet>F{D}, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(rule bisim1_bisims1.bisim1FAcc)
    with red \<tau> show ?thesis by(fastforce intro: FAcc1Red elim!: FAcc_\<tau>red1r_xt FAcc_\<tau>red1t_xt simp add: no_call2_def)
  next
    case False
    with pc have pc: "pc = length (compE2 e)" by auto
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len bsok have "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (e'\<bullet>F{D}, xs) (Val v\<bullet>F{D}, loc)" by(rule FAcc_\<tau>red1r_xt)
    moreover have \<tau>: "\<not> \<tau>move2 (compP2 P) h [v] (e\<bullet>F{D}) (length (compE2 e)) None" by(simp add: \<tau>move2_iff)
    moreover have "\<exists>ta' e''. P,e\<bullet>F{D},h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> True,P,t \<turnstile>1 \<langle>Val v\<bullet>F{D}, (h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim wbisim1 (extTA2J1 P ta') ta"
    proof(cases "v = Null")
      case True with exec stk xcp pc show ?thesis
        by(fastforce elim!: exec_meth.cases simp add: exec_move_def intro: bisim1FAccNull Red1FAccNull)
    next
      case False
      with exec stk xcp pc \<open>P,h \<turnstile> stk [:\<le>] ST\<close>
      obtain A where [simp]: "v = Addr A"
        by(fastforce simp add: exec_move_def exec_meth_instr is_Ref_def compP2_def)
      from exec False pc stk xcp obtain v' where v': "heap_read h A (CField D F) v'" "stk' = [v']"
        by(auto simp add: exec_move_def exec_meth_instr)
      have "P,e\<bullet>F{D},h' \<turnstile> (Val v',loc) \<leftrightarrow> ([v'], loc, length (compE2 (e\<bullet>F{D})), None)"
        by(rule bisim1Val2) simp
      thus ?thesis using exec stk xcp pc v'
        by(fastforce elim!: exec_meth.cases intro: Red1FAcc simp add: exec_move_def ta_upd_simps ta_bisim_def)
    qed
    ultimately show ?thesis using \<tau> pc xcp stk by(fastforce elim!: rtranclp_trans simp add: no_call2_def)
  qed
next
  case (bisim1FAccThrow e n a xs stk loc pc F D)
  note exec = \<open>?exec (e\<bullet>F{D}) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim1 have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False by(auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1FAccNull e n F D xs)
  note exec = \<open>?exec (e\<bullet>F{D}) [Null] xs (length (compE2 e)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'\<close>
  hence False by(auto elim!: exec_meth.cases dest!: match_ex_table_pc_length_compE2 simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1FAss1 e n e' xs stk loc pc xcp e2 F D)
  note IH1 = bisim1FAss1.IH(2)
  note IH2 = bisim1FAss1.IH(4)
  note exec = \<open>?exec (e\<bullet>F{D} := e2) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note len = \<open>n + max_vars (e'\<bullet>F{D} := e2) \<le> length xs\<close>
  note bsok = \<open>bsok (e\<bullet>F{D} := e2) n\<close>
  from bisim1 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_FAss1)
    from True have \<tau>: "\<tau>move2 (compP2 P) h stk (e\<bullet>F{D} := e2) pc xcp = \<tau>move2 (compP2 P) h stk e pc xcp"
      by(simp add: \<tau>move2_iff)
    with IH1[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain e'' xs''
      where bisim': "P,e,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red e' xs e'' xs'' e stk pc pc' xcp xcp'" by auto
    from bisim' have "P,e\<bullet>F{D} := e2,h' \<turnstile> (e''\<bullet>F{D} := e2, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(rule bisim1_bisims1.bisim1FAss1)
    with red \<tau> show ?thesis by(fastforce intro: FAss1Red1 elim!: FAss_\<tau>red1r_xt1 FAss_\<tau>red1t_xt1 simp add: no_call2_def)
  next
    case False
    with pc have pc: "pc = length (compE2 e)" by auto
    with bisim1 obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len bsok have rede1': "\<tau>red1r P t h (e', xs) (Val v, loc)" 
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (e'\<bullet>F{D} := e2, xs) (Val v\<bullet>F{D} := e2, loc)" by(rule FAss_\<tau>red1r_xt1)
    moreover from pc exec stk xcp
    have exec': "exec_meth_d (compP2 P) (compE2 e @ compE2 e2 @ [Putfield F D, Push Unit]) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxE2 e2 0 0))) t h ([] @ [v], loc, length (compE2 e) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
    hence "exec_meth_d (compP2 P) (compE2 e2 @ [Putfield F D, Push Unit]) (stack_xlift (length [v]) (compxE2 e2 0 0)) t h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length [v]) (compxE2 e2 0 0)) t h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_take) simp
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move_d P t e2 h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 e), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    with pc xcp have \<tau>: "\<tau>move2 (compP2 P) h [v] (e\<bullet>F{D} := e2) (length (compE2 e)) None = \<tau>move2 (compP2 P) h [] e2 0 None"
      using \<tau>instr_stk_drop_exec_move[where stk="[]" and vs = "[v]"] by(simp add: \<tau>move2_iff)
    from bisim1 have "length xs = length loc" by(rule bisim1_length_xs)
    with IH2[OF exec'', of "[]"] len bsok obtain e'' xs''
      where bisim': "P,e2,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 e), xcp')"
      and red: "?red e2 loc e'' xs'' e2 [] 0 (pc' - length (compE2 e)) None xcp'" by auto
    from bisim' 
    have "P,e\<bullet>F{D} := e2,h' \<turnstile> (Val v\<bullet>F{D} := e'', xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
      by(rule bisim1_bisims1.bisim1FAss2)
    moreover from red \<tau> 
    have "?red (Val v\<bullet>F{D} := e2) loc (Val v\<bullet>F{D} := e'') xs'' (e\<bullet>F{D} := e2) [v] (length (compE2 e)) pc' None xcp'"
      by(fastforce intro: FAss1Red2 elim!: FAss_\<tau>red1r_xt2 FAss_\<tau>red1t_xt2 split: if_split_asm simp add: no_call2_def)
    moreover from exec' have "pc' \<ge> length (compE2 e)"
      by(rule exec_meth_drop_xt_pc) auto
    moreover have "no_call2 (e\<bullet>F{D} := e2) pc" using pc by(simp add: no_call2_def)
    ultimately show ?thesis using \<tau> stk' pc xcp stk by(fastforce elim!: rtranclp_trans)
  qed
next
  case (bisim1FAss2 e2 n e' xs stk loc pc xcp e F D v)
  note IH2 = bisim1FAss2.IH(2)
  note exec = \<open>?exec (e\<bullet>F{D} := e2) (stk @ [v]) loc (length (compE2 e) + pc) xcp stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars (Val v\<bullet>F{D} := e') \<le> length xs\<close>
  note bsok = \<open>bsok (e\<bullet>F{D} := e2) n\<close>
  note ST = \<open>P,h \<turnstile> stk @ [v] [:\<le>] ST\<close>
  then obtain T ST' where ST': "P,h \<turnstile> stk [:\<le>] ST'" and T: "typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>"
    by(auto simp add: list_all2_append1 list_all2_Cons1 conf_def)

  from bisim2 have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    from exec have exec': "exec_meth_d (compP2 P) (compE2 e @ compE2 e2 @ [Putfield F D, Push Unit]) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxE2 e2 0 0))) t h (stk @ [v], loc, length (compE2 e) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2 exec_move_def)
    hence "exec_meth_d (compP2 P) (compE2 e2 @ [Putfield F D, Push Unit]) (stack_xlift (length [v]) (compxE2 e2 0 0)) t h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth_d (compP2 P) (compE2 e2) (stack_xlift (length [v]) (compxE2 e2 0 0)) t h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
      using True by(rule exec_meth_take)
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move_d P t e2 h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    with True have \<tau>: "\<tau>move2 (compP2 P) h (stk @ [v]) (e\<bullet>F{D} := e2) (length (compE2 e) + pc) xcp = \<tau>move2 (compP2 P) h stk e2 pc xcp"
      by(auto simp add: \<tau>move2_iff \<tau>instr_stk_drop_exec_move)
    moreover from IH2[OF exec'' _ _ ST' \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain e'' xs''
      where bisim': "P,e2,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 e), xcp')"
      and red: "?red e' xs e'' xs'' e2 stk pc (pc' - length (compE2 e)) xcp xcp'" by auto
    from bisim' have "P,e\<bullet>F{D} := e2,h' \<turnstile> (Val v\<bullet>F{D} := e'', xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
      by(rule bisim1_bisims1.bisim1FAss2)
    moreover from exec' have "pc' \<ge> length (compE2 e)"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using red \<tau> stk' True
      by(fastforce intro: FAss1Red2 elim!: FAss_\<tau>red1r_xt2 FAss_\<tau>red1t_xt2 split: if_split_asm simp add: no_call2_def)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e2)" by simp
    with bisim2 obtain v2 where stk: "stk = [v2]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim2 pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v2, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (Val v\<bullet>F{D} := e', xs) (Val v\<bullet>F{D} := Val v2, loc)" by(rule FAss_\<tau>red1r_xt2)
    moreover have \<tau>: "\<not> \<tau>move2 (compP2 P) h [v2, v] (e\<bullet>F{D} := e2) (length (compE2 e) + length (compE2 e2)) None" by(simp add: \<tau>move2_iff)
    moreover
    have "\<exists>ta' e''. P,e\<bullet>F{D} := e2,h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> True,P,t \<turnstile>1 \<langle>Val v\<bullet>F{D} := Val v2, (h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim wbisim1 (extTA2J1 P ta') ta"
    proof(cases "v = Null")
      case True with exec stk xcp show ?thesis
        by(fastforce elim!: exec_meth.cases simp add: exec_move_def intro: bisim1FAssNull Red1FAssNull)
    next
      case False with exec stk xcp T show ?thesis
        by(fastforce simp add: exec_move_def compP2_def exec_meth_instr is_Ref_def ta_upd_simps ta_bisim_def intro: bisim1FAss3 Red1FAss)
    qed
    ultimately show ?thesis using exec xcp stk by(fastforce simp add: no_call2_def)
  qed
next
  case (bisim1FAssThrow1 e n a xs stk loc pc e2 F D)
  note exec = \<open>?exec (e\<bullet>F{D} := e2) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim1 have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: exec_move_def match_ex_table_not_pcs_None)
  thus ?case ..
next
  case (bisim1FAssThrow2 e2 n a xs stk loc pc e F D v)
  note exec = \<open>?exec (e\<bullet>F{D} := e2) (stk @ [v]) loc (length (compE2 e) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  hence "match_ex_table (compP2 P) (cname_of h a) (length (compE2 e) + pc) (compxE2 e2 (length (compE2 e)) 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec have False
    by(auto elim!: exec_meth.cases simp add: compxE2_stack_xlift_convs exec_move_def)(auto dest!: match_ex_table_stack_xliftD simp add: match_ex_table_append_not_pcs)
  thus ?case ..
next
  case (bisim1FAssNull e n e2 F D xs v)
  note exec = \<open>?exec (e\<bullet>F{D} := e2) [v, Null] xs (length (compE2 e) + length (compE2 e2)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'\<close>
  hence False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs compxE2_size_convs exec_move_def
               dest!: match_ex_table_shift_pcD match_ex_table_pc_length_compE2)
  thus ?case ..
next
  case (bisim1FAss3 e n e2 F D xs)
  have "P,e\<bullet>F{D} := e2,h \<turnstile> (unit, xs) \<leftrightarrow> ([Unit], xs, length (compE2 (e\<bullet>F{D} := e2)), None)" by(rule bisim1Val2) simp
  moreover have "\<tau>move2 (compP2 P) h [] (e\<bullet>F{D} := e2) (Suc (length (compE2 e) + length (compE2 e2))) None" by(simp add: \<tau>move2_iff)
  moreover note \<open>?exec (e\<bullet>F{D} := e2) [] xs (Suc (length (compE2 e) + length (compE2 e2))) None stk' loc' pc' xcp'\<close>
  ultimately show ?case
    by(fastforce elim!: exec_meth.cases simp add: ac_simps exec_move_def)
next
  case (bisim1CAS1 a n a' xs stk loc pc xcp i e D F)
  note IH1 = bisim1CAS1.IH(2)
  note IH2 = bisim1CAS1.IH(4)
  note exec = \<open>?exec (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,a,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note len = \<open>n + max_vars _ \<le> length xs\<close>
  note bsok = \<open>bsok (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) n\<close>
  from bisim1 have pc: "pc \<le> length (compE2 a)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 a)")
    case True
    with exec have exec': "?exec a stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_CAS1)
    from True have \<tau>: "\<tau>move2 (compP2 P) h stk (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) pc xcp = \<tau>move2 (compP2 P) h stk a pc xcp" by(simp add: \<tau>move2_iff)
    with IH1[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain e'' xs''
      where bisim': "P,a,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red a' xs e'' xs'' a stk pc pc' xcp xcp'" by auto
    from bisim' have "P,a\<bullet>compareAndSwap(D\<bullet>F, i, e),h' \<turnstile> (e''\<bullet>compareAndSwap(D\<bullet>F, i, e), xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(rule bisim1_bisims1.bisim1CAS1)
    moreover from True have "no_call2 (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) pc = no_call2 a pc" by(simp add: no_call2_def)
    ultimately show ?thesis using red \<tau> by(fastforce intro: CAS1Red1 elim!: CAS_\<tau>red1r_xt1 CAS_\<tau>red1t_xt1)
  next
    case False
    with pc have pc: "pc = length (compE2 a)" by auto
    with bisim1 obtain v where a': "is_val a' \<longrightarrow> a' = Val v" 
      and stk: "stk = [v]" and xcp: "xcp = None" and call: "call1 a' = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len bsok have rede1': "\<tau>red1r P t h (a', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (a'\<bullet>compareAndSwap(D\<bullet>F, i, e), xs) (Val v\<bullet>compareAndSwap(D\<bullet>F, i, e), loc)" by(rule CAS_\<tau>red1r_xt1)
    moreover from pc exec stk xcp
    have exec': "exec_meth_d (compP2 P) (compE2 a @ compE2 i @ compE2 e @ [CAS F D]) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0) @ shift (length (compE2 i)) (compxE2 e 0 (Suc (Suc 0))))) t h ([] @ [v], loc, length (compE2 a) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
    hence "exec_meth_d (compP2 P) (compE2 i @ compE2 e @ [CAS F D]) (stack_xlift (length [v]) (compxE2 i 0 0) @ shift (length (compE2 i)) (compxE2 e 0 (Suc (Suc 0)))) t h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth_d (compP2 P) (compE2 i) (stack_xlift (length [v]) (compxE2 i 0 0)) t h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_take_xt) simp
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move_d P t i h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 a), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    with pc xcp have \<tau>: "\<tau>move2 (compP2 P) h [v] (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) (length (compE2 a)) None = \<tau>move2 (compP2 P) h [] i 0 None"
      using \<tau>instr_stk_drop_exec_move[where stk="[]" and vs="[v]"]
      by(auto simp add: \<tau>move2_iff)
    from bisim1 have "length xs = length loc" by(rule bisim1_length_xs)
    with IH2[OF exec''] len bsok obtain e'' xs''
      where bisim': "P,i,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a), xcp')"
      and red: "?red i loc e'' xs'' i [] 0 (pc' - length (compE2 a)) None xcp'" by fastforce
    from bisim'
    have "P,a\<bullet>compareAndSwap(D\<bullet>F, i, e),h' \<turnstile> (Val v\<bullet>compareAndSwap(D\<bullet>F, e'', e), xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule bisim1_bisims1.bisim1CAS2)
    moreover from red \<tau> have "?red (Val v\<bullet>compareAndSwap(D\<bullet>F, i, e)) loc (Val v\<bullet>compareAndSwap(D\<bullet>F, e'', e)) xs'' (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) [v] (length (compE2 a)) pc' None xcp'"
      by(fastforce intro: CAS1Red2 elim!: CAS_\<tau>red1r_xt2 CAS_\<tau>red1t_xt2 split: if_split_asm simp add: no_call2_def)
    moreover from exec' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc) auto
    moreover have "no_call2 (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) pc" using pc by(simp add: no_call2_def)
    ultimately show ?thesis using \<tau> stk' pc xcp stk by(fastforce elim!: rtranclp_trans)
  qed
next
  case (bisim1CAS2 i n i' xs stk loc pc xcp a e D F v)
  note IH2 = bisim1CAS2.IH(2)
  note IH3 = bisim1CAS2.IH(6)
  note exec = \<open>?exec (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) (stk @ [v]) loc (length (compE2 a) + pc) xcp stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim3 = \<open>P,e,h \<turnstile> (e, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
  note len = \<open>n + max_vars (Val v\<bullet>compareAndSwap(D\<bullet>F, i', e)) \<le> length xs\<close>
  note bsok = \<open>bsok (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) n\<close>
  from bisim2 have pc: "pc \<le> length (compE2 i)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 i)")
    case True
    from exec have exec': "exec_meth_d (compP2 P) (compE2 a @ compE2 i @ compE2 e @ [CAS F D]) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0) @ shift (length (compE2 i)) (compxE2 e 0 (Suc (Suc 0))))) t h (stk @ [v], loc, length (compE2 a) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2 ac_simps exec_move_def)
    hence "exec_meth_d (compP2 P) (compE2 i @ compE2 e @ [CAS F D]) (stack_xlift (length [v]) (compxE2 i 0 0) @ shift (length (compE2 i)) (compxE2 e 0 (Suc (Suc 0)))) t h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth_d (compP2 P) (compE2 i) (stack_xlift (length [v]) (compxE2 i 0 0)) t h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      using True by(rule exec_meth_take_xt)
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move_d P t i h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    with True have \<tau>: "\<tau>move2 (compP2 P) h (stk @ [v]) (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) (length (compE2 a) + pc) xcp = \<tau>move2 (compP2 P) h stk i pc xcp"
      by(auto simp add: \<tau>move2_iff \<tau>instr_stk_drop_exec_move)
    moreover from \<open>P,h \<turnstile> stk @ [v] [:\<le>] ST\<close> obtain ST2 where "P,h \<turnstile> stk [:\<le>] ST2" by(auto simp add: list_all2_append1)
    from IH2[OF exec'' _ _ this \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain e'' xs''
      where bisim': "P,i,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a), xcp')"
      and red: "?red i' xs e'' xs'' i stk pc (pc' - length (compE2 a)) xcp xcp'" by fastforce
    from bisim'
    have "P,a\<bullet>compareAndSwap(D\<bullet>F, i, e),h' \<turnstile> (Val v\<bullet>compareAndSwap(D\<bullet>F, e'', e), xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule bisim1_bisims1.bisim1CAS2)
    moreover from exec' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc) auto
    moreover have "no_call2 i pc \<Longrightarrow> no_call2 (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) (length (compE2 a) + pc)" by(simp add: no_call2_def)
    ultimately show ?thesis using red \<tau> stk' True
      by(fastforce intro: CAS1Red2 elim!: CAS_\<tau>red1r_xt2 CAS_\<tau>red1t_xt2 split: if_split_asm)
  next
    case False
    with pc have [simp]: "pc = length (compE2 i)" by simp
    with bisim2 obtain v2 where i': "is_val i' \<longrightarrow> i' = Val v2" 
      and stk: "stk = [v2]" and xcp: "xcp = None" and call: "call1 i' = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim2 pc len bsok have red: "\<tau>red1r P t h (i', xs) (Val v2, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (Val v\<bullet>compareAndSwap(D\<bullet>F, i', e ), xs) (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v2, e), loc)" by(rule CAS_\<tau>red1r_xt2)
    moreover from pc exec stk xcp
    have exec': "exec_meth_d (compP2 P) ((compE2 a @ compE2 i) @ compE2 e @ [CAS F D]) ((compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0)) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length [v2, v]) (compxE2 e 0 0))) t h ([] @ [v2, v], loc, length (compE2 a @ compE2 i) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
    hence "exec_meth_d (compP2 P) (compE2 e @ [CAS F D]) (stack_xlift (length [v2, v]) (compxE2 e 0 0)) t h ([] @ [v2, v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth_d (compP2 P) (compE2 e) (stack_xlift (length [v2, v]) (compxE2 e 0 0)) t h ([] @ [v2, v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      by(rule exec_meth_take) simp
    with bisim3 obtain stk'' where stk': "stk' = stk'' @ [v2, v]"
      and exec'': "exec_move_d P t e h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    with pc xcp have \<tau>: "\<tau>move2 (compP2 P) h [v2, v] (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) (length (compE2 a) + length (compE2 i)) None = \<tau>move2 (compP2 P) h [] e 0 None"
      using \<tau>instr_stk_drop_exec_move[where stk="[]" and vs="[v2, v]"] by(simp add: \<tau>move2_iff)
    from bisim2 have "length xs = length loc" by(rule bisim1_length_xs)
    with IH3[OF exec'', of "[]"] len bsok obtain e'' xs''
      where bisim': "P,e,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a) - length (compE2 i), xcp')"
      and red: "?red e loc e'' xs'' e [] 0 (pc' - length (compE2 a) - length (compE2 i)) None xcp'"
      by auto (fastforce simp only: length_append diff_diff_left)
    from bisim'
    have "P,a\<bullet>compareAndSwap(D\<bullet>F, i, e),h' \<turnstile> (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v2, e''), xs'') \<leftrightarrow> (stk'' @ [v2, v], loc', length (compE2 a) + length (compE2 i) + (pc' - length (compE2 a) - length (compE2 i)), xcp')"
      by(rule bisim1_bisims1.bisim1CAS3)
    moreover from red \<tau>
    have "?red (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v2, e)) loc (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v2, e'')) xs'' (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) [v2, v] (length (compE2 a) + length (compE2 i)) pc' None xcp'"
      by(fastforce intro: CAS1Red3 elim!: CAS_\<tau>red1r_xt3 CAS_\<tau>red1t_xt3 split: if_split_asm simp add: no_call2_def)
    moreover from exec' have "pc' \<ge> length (compE2 a @ compE2 i)"
      by(rule exec_meth_drop_xt_pc) auto
    moreover have "no_call2 (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) (length (compE2 a) + pc)" by(simp add: no_call2_def)
    ultimately show ?thesis using \<tau> stk' pc xcp stk by(fastforce elim!: rtranclp_trans)
  qed
next
  case (bisim1CAS3 e n e' xs stk loc pc xcp a i D F v v')
  note IH3 = bisim1CAS3.IH(2)
  note exec = \<open>?exec (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) (stk @ [v', v]) loc (length (compE2 a) + length (compE2 i) + pc) xcp stk' loc' pc' xcp'\<close>
  note bisim3 = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars _ \<le> length xs\<close>
  note bsok = \<open>bsok (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) n\<close>
  from \<open>P,h \<turnstile> stk @ [v', v] [:\<le>] ST\<close> obtain T T' ST'
    where [simp]: "ST = ST' @ [T', T]"
    and wtv: "P,h \<turnstile> v :\<le> T" and wtv': "P,h \<turnstile> v' :\<le> T'" and ST': "P,h \<turnstile> stk [:\<le>] ST'"
    by(auto simp add: list_all2_Cons1 list_all2_append1)
  from bisim3 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    from exec have exec': "exec_meth_d (compP2 P) ((compE2 a @ compE2 i) @ compE2 e @ [CAS F D]) ((compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0)) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length [v', v]) (compxE2 e 0 0))) t h (stk @ [v', v], loc, length (compE2 a @ compE2 i) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2 exec_move_def)
    hence "exec_meth_d (compP2 P) (compE2 e @ [CAS F D]) (stack_xlift (length [v', v]) (compxE2 e 0 0)) t h (stk @ [v', v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth_d (compP2 P) (compE2 e) (stack_xlift (length [v', v]) (compxE2 e 0 0)) t h (stk @ [v', v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      using True by(rule exec_meth_take)
    with bisim3 obtain stk'' where stk': "stk' = stk'' @ [v', v]"
      and exec'': "exec_move_d P t e h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    with True have \<tau>: "\<tau>move2 (compP2 P) h (stk @ [v', v]) (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) (length (compE2 a) + length (compE2 i) + pc) xcp = \<tau>move2 (compP2 P) h stk e pc xcp"
      by(auto simp add: \<tau>move2_iff \<tau>instr_stk_drop_exec_move)
    moreover from IH3[OF exec'' _ _ ST' \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain e'' xs''
      where bisim': "P,e,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a) - length (compE2 i), xcp')"
      and red: "?red e' xs e'' xs'' e stk pc (pc' - length (compE2 a) - length (compE2 i)) xcp xcp'"
      by auto(fastforce simp only: length_append diff_diff_left)
    from bisim'
    have "P,a\<bullet>compareAndSwap(D\<bullet>F, i, e),h' \<turnstile> (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e''), xs'') \<leftrightarrow> (stk'' @ [v', v], loc', length (compE2 a) + length (compE2 i) + (pc' - length (compE2 a) - length (compE2 i)), xcp')"
      by(rule bisim1_bisims1.bisim1CAS3)
    moreover from exec' have "pc' \<ge> length (compE2 a @ compE2 i)"
      by(rule exec_meth_drop_xt_pc) auto
    moreover have "no_call2 e pc \<Longrightarrow> no_call2 (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) (length (compE2 a) + length (compE2 i) + pc)"
      by(simp add: no_call2_def)
    ultimately show ?thesis using red \<tau> stk' True
      by(fastforce intro: CAS1Red3 elim!: CAS_\<tau>red1r_xt3 CAS_\<tau>red1t_xt3 split: if_split_asm)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim3 obtain v2 where stk: "stk = [v2]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim3 pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v2, loc)" 
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e'), xs) (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', Val v2), loc)" by(rule CAS_\<tau>red1r_xt3)
    moreover have \<tau>: "\<not> \<tau>move2 (compP2 P) h [v2, v', v] (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None"
      by(simp add: \<tau>move2_iff)
    moreover 
    have "\<exists>ta' e''. P,a\<bullet>compareAndSwap(D\<bullet>F, i, e),h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> True,P,t \<turnstile>1 \<langle>Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', Val v2), (h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim wbisim1 (extTA2J1 P ta') ta"
    proof(cases "v = Null")
      case True with exec stk xcp show ?thesis
        by(fastforce elim!: exec_meth.cases simp add: exec_move_def intro: bisim1CASFail CAS1Null)
    next
      case False
      have "P,a\<bullet>compareAndSwap(D\<bullet>F, i, e),h' \<turnstile> (Val (Bool b), loc) \<leftrightarrow> ([Bool b], loc, length (compE2 (a\<bullet>compareAndSwap(D\<bullet>F, i, e))), None)" for b
        by(rule bisim1Val2) simp
      with False exec stk xcp show ?thesis
        by(auto elim!: exec_meth.cases simp add: exec_move_def is_Ref_def ac_simps intro: Red1CASSucceed Red1CASFail)
          (fastforce intro!: Red1CASSucceed Red1CASFail simp add: ta_bisim_def)+
    qed
    ultimately show ?thesis using exec xcp stk by(fastforce simp add: no_call2_def)
  qed
next
  case (bisim1CASThrow1 A n a xs stk loc pc i e D F)
  note exec = \<open>?exec (A\<bullet>compareAndSwap(D\<bullet>F, i, e)) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,A,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim1 have pc: "pc < length (compE2 A)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 A 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
  thus ?case ..
next
  case (bisim1CASThrow2 i n a xs stk loc pc A e D F v)
  note exec = \<open>?exec (A\<bullet>compareAndSwap(D\<bullet>F, i, e)) (stk @ [v]) loc (length (compE2 A) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,i,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim2 have pc: "pc < length (compE2 i)" by(auto dest: bisim1_ThrowD)
  from bisim2 have "match_ex_table (compP2 P) (cname_of h a) (length (compE2 A) + pc) (compxE2 i (length (compE2 A)) 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False
    apply(auto elim!: exec_meth.cases simp add: compxE2_stack_xlift_convs compxE2_size_convs exec_move_def)
    apply(auto simp add: match_ex_table_append_not_pcs)
    done
  thus ?case .. 
next
  case (bisim1CASThrow3 e n a xs stk loc pc A i D F v' v)
  note exec = \<open>?exec (A\<bullet>compareAndSwap(D\<bullet>F, i, e)) (stk @ [v', v]) loc (length (compE2 A) + length (compE2 i) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim2 have "match_ex_table (compP2 P) (cname_of h a) (length (compE2 A) + length (compE2 i) + pc) (compxE2 e (length (compE2 A) + length (compE2 i)) 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec have False
    apply(auto elim!: exec_meth.cases simp add: compxE2_stack_xlift_convs compxE2_size_convs exec_move_def)
    apply(auto dest!: match_ex_table_stack_xliftD match_ex_table_shift_pcD dest: match_ex_table_pcsD simp add: match_ex_table_append match_ex_table_shift_pc_None)
    done
  thus ?case .. 
next
  case (bisim1CASFail a n i e D F ad xs v' v v'')
  note exec = \<open>?exec (a\<bullet>compareAndSwap(D\<bullet>F, i, e)) [v', v, v''] xs (length (compE2 a) + length (compE2 i) + length (compE2 e)) \<lfloor>ad\<rfloor> stk' loc' pc' xcp'\<close>
  hence False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_append exec_move_def
            dest!: match_ex_table_shift_pcD match_ex_table_pc_length_compE2)
  thus ?case ..
next
  case (bisim1Call1 obj n obj' xs stk loc pc xcp ps M')
  note IH1 = bisim1Call1.IH(2)
  note IH2 = bisim1Call1.IH(4)
  note exec = \<open>?exec (obj\<bullet>M'(ps)) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,obj,h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim2 = \<open>P,ps,h \<turnstile> (ps, loc) [\<leftrightarrow>] ([], loc, 0, None)\<close>
  note len = \<open>n + max_vars (obj'\<bullet>M'(ps)) \<le> length xs\<close>
  note bsok = \<open>bsok (obj\<bullet>M'(ps)) n\<close>
  from bisim1 have pc: "pc \<le> length (compE2 obj)" by(rule bisim1_pc_length_compE2)
  from bisim1 have lenxs: "length xs = length loc" by(rule bisim1_length_xs)
  show ?case
  proof(cases "pc < length (compE2 obj)")
    case True
    with exec have exec': "?exec obj stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_Call1)
    from True have "\<tau>move2 (compP2 P) h stk (obj\<bullet>M'(ps)) pc xcp = \<tau>move2 (compP2 P) h stk obj pc xcp" by(simp add: \<tau>move2_iff)
    moreover from True have "no_call2 (obj\<bullet>M'(ps)) pc = no_call2 obj pc" by(simp add: no_call2_def)
    ultimately show ?thesis 
      using IH1[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] bisim2 len bsok
      by(fastforce intro: bisim1_bisims1.bisim1Call1 Call1Obj elim!: Call_\<tau>red1r_obj Call_\<tau>red1t_obj)
  next
    case False
    with pc have pc: "pc = length (compE2 obj)" by auto
    with bisim1 obtain v where stk: "stk = [v]" and xcp: "xcp = None" and call: "call1 obj' = None"
      and v: "is_val obj' \<Longrightarrow> obj' = Val v \<and> xs = loc"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len bsok have "\<tau>red1r P t h (obj', xs) (Val v, loc)" 
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence red: "\<tau>red1r P t h (obj'\<bullet>M'(ps), xs) (Val v\<bullet>M'(ps), loc)" by(rule Call_\<tau>red1r_obj)
    show ?thesis
    proof(cases ps)
      case (Cons p ps')
      from pc exec stk xcp
      have "exec_meth_d (compP2 P) (compE2 (obj\<bullet>M'(ps))) (compxE2 (obj\<bullet>M'(ps)) 0 0) t h ([] @ [v], loc, length (compE2 obj) + 0, None) ta h' (stk', loc', pc', xcp')"
        by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
      hence exec': "exec_meth_d (compP2 P) (compEs2 ps) (stack_xlift (length [v]) (compxEs2 ps 0 0)) t h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 obj), xcp')"
        and pc': "pc' \<ge> length (compE2 obj)" using Cons
        by(safe dest!: Call_execParamD) simp_all
      from exec' bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
        and exec'': "exec_moves_d P t ps h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 obj), xcp')"
        unfolding exec_moves_def by -(drule (1) exec_meth_stk_splits, auto)
      with pc xcp have \<tau>: "\<tau>move2 (compP2 P) h [v] (obj\<bullet>M'(ps)) (length (compE2 obj)) None = \<tau>moves2 (compP2 P) h [] ps 0 None"
        using \<tau>instr_stk_drop_exec_moves[where stk="[]" and vs="[v]"]
        by(auto simp add: \<tau>move2_iff \<tau>moves2_iff)
      from IH2[OF exec'', of "[]"] len lenxs bsok obtain es'' xs''
        where bisim': "P,ps,h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk'', loc', pc' - length (compE2 obj), xcp')"
        and red': "?reds ps loc es'' xs'' ps [] 0 (pc' - length (compE2 obj)) None xcp'" by auto
      from bisim' have "P,obj\<bullet>M'(ps),h' \<turnstile> (Val v\<bullet>M'(es''), xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 obj) + (pc' - length (compE2 obj)), xcp')"
        by(rule bisim1CallParams)
      moreover from pc Cons have "no_call2 (obj\<bullet>M'(ps)) pc" by(simp add: no_call2_def)
      ultimately show ?thesis using red red' \<tau> stk' pc xcp pc' stk call
        by(fastforce elim!: rtranclp_trans Call_\<tau>red1r_param Call_\<tau>red1t_param intro: Call1Params rtranclp_tranclp_tranclp split: if_split_asm)
    next
      case [simp]: Nil
      from exec pc stk xcp
      have "v = Null \<or> (is_Addr v \<and> (\<exists>T C' Ts' Tr' D'. typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor> \<and> class_type_of' T = \<lfloor>C'\<rfloor> \<and> P \<turnstile> C' sees M':Ts'\<rightarrow>Tr' = Native in D'))" (is "_ \<or> ?rest")
        by(fastforce elim!: exec_meth.cases simp add: is_Ref_def exec_move_def compP2_def has_method_def split: if_split_asm)
      thus ?thesis
      proof
        assume [simp]: "v = Null"
        have "P,obj\<bullet>M'([]),h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([] @ [Null], loc, length (compE2 obj) + length (compEs2 ([]  :: 'addr expr1 list)), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
          by(safe intro!: bisim1CallThrow) simp_all
        moreover have "True,P,t \<turnstile>1 \<langle>null\<bullet>M'(map Val []),(h, loc)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer,(h, loc)\<rangle>"
          by(rule Red1CallNull)
        moreover have "\<tau>move1 P h (Val v\<bullet>M'([]))" "\<tau>move2 (compP2 P) h [Null] (obj\<bullet>M'(ps)) (length (compE2 obj)) None"
          by(simp_all add: \<tau>move2_iff)
        ultimately show ?thesis using exec pc stk xcp red
          by(fastforce elim!: exec_meth.cases intro: rtranclp_trans simp add: exec_move_def)
      next
        assume ?rest
        then obtain a Ta Ts' Tr' D' where [simp]: "v = Addr a"
          and Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>"
          and iec: "P \<turnstile> class_type_of Ta sees M': Ts'\<rightarrow>Tr' = Native in D'" by auto
        with exec pc stk xcp
        obtain ta' va h'' U where redex: "(ta', va, h'') \<in> red_external_aggr (compP2 P) t a M' [] h"
          and ret: "(xcp', h', [(stk', loc', undefined, undefined, pc')]) = extRet2JVM 0 h'' [Addr a] loc undefined undefined (length (compE2 obj)) [] va"
          and wtext': "P,h \<turnstile> a\<bullet>M'([]) : U"
          and ta': "ta = extTA2JVM (compP2 P) ta'"
          by(fastforce simp add: is_Ref_def exec_move_def compP2_def external_WT'_iff exec_meth_instr)
        from Ta iec have \<tau>: "\<tau>move1 P h (Val v\<bullet>M'([])) \<longleftrightarrow> \<tau>move2 (compP2 P) h [Addr a] (obj\<bullet>M'(ps)) (length (compE2 obj)) None"
          by(auto simp add: \<tau>move2_iff compP2_def)
        from ret have [simp]: "h'' = h'" by simp
        from wtext' have wtext'': "compP2 P,h \<turnstile> a\<bullet>M'([]) : U" by(simp add: external_WT'_iff compP2_def)
        from wf have "wf_jvm_prog (compP2 P)" by(rule wt_compP2)
        then obtain wf_md where wf': "wf_prog wf_md (compP2 P)"
          unfolding wf_jvm_prog_def by(blast dest: wt_jvm_progD)
        from tconf have tconf': "compP2 P,h \<turnstile> t \<surd>t" by(simp add: compP2_def tconf_def)
        from redex have redex'': "compP2 P,t \<turnstile> \<langle>a\<bullet>M'([]), h\<rangle> -ta'\<rightarrow>ext \<langle>va, h'\<rangle>"
          by(simp add: WT_red_external_list_conv[OF wf' wtext'' tconf', symmetric])
        hence redex': "P,t \<turnstile> \<langle>a\<bullet>M'([]), h\<rangle> -ta'\<rightarrow>ext \<langle>va, h'\<rangle>" by(simp add: compP2_def)
        with Ta iec have "True,P,t \<turnstile>1 \<langle>addr a\<bullet>M'(map Val []), (h, loc)\<rangle> -ta'\<rightarrow> \<langle>extRet2J (addr a\<bullet>M'(map Val [])) va, (h', loc)\<rangle>"
          by -(rule Red1CallExternal, auto)
        moreover have "P,obj\<bullet>M'(ps),h' \<turnstile> (extRet2J (addr a\<bullet>M'(map Val [])) va, loc) \<leftrightarrow> (stk', loc', pc', xcp')"
        proof(cases va)
          case (RetVal v)
          have "P,obj\<bullet>M'([]),h' \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (obj\<bullet>M'([]))), None)"
            by(rule bisim1Val2) simp
          with ret RetVal show ?thesis by simp
        next
          case (RetExc ad)
          have "P,obj\<bullet>M'([]),h' \<turnstile> (Throw ad, loc) \<leftrightarrow> ([] @ [v], loc, length (compE2 (obj)) + length (compEs2 ([] :: 'addr expr1 list)), \<lfloor>ad\<rfloor>)"
            by(rule bisim1CallThrow) simp
          with ret RetExc show ?thesis by simp
        next
          case RetStaySame
          have "P,obj\<bullet>M'([]),h' \<turnstile> (addr a\<bullet>M'([]), loc) \<leftrightarrow> ([Addr a], loc, length (compE2 obj), None)"
            by(rule bisim1_bisims1.bisim1Call1)(rule bisim1Val2, simp)
          thus ?thesis using ret RetStaySame by simp
        qed
        moreover from \<open>preallocated h\<close> red_external_hext[OF redex'] have "preallocated h'" by(rule preallocated_hext) 
        from redex'' wtext'' \<open>hconf h\<close> have "hconf h'" by(rule external_call_hconf)
        with ta' redex' \<open>preallocated h'\<close>
        have "ta_bisim wbisim1 (extTA2J1 P ta') ta" by(auto intro: red_external_ta_bisim21[OF wf])
        moreover have "\<tau>move1 P h (Val v\<bullet>M'([])) \<Longrightarrow> ta' = \<epsilon> \<and> h' = h" using redex' Ta iec
          by(fastforce dest: \<tau>external'_red_external_heap_unchanged \<tau>external'_red_external_TA_empty sees_method_fun simp add: \<tau>external'_def \<tau>external_def)
        moreover from v call
        have "call1 (obj'\<bullet>M'(ps)) \<noteq> None \<Longrightarrow> Val v\<bullet>M'(ps) = obj'\<bullet>M'(ps) \<and> loc = xs"
          by(auto split: if_split_asm)
        ultimately show ?thesis using red \<tau> pc xcp stk Ta call iec
          apply(auto simp del: call1.simps calls1.simps)
          apply(rule exI conjI|assumption|erule rtranclp.rtrancl_into_rtrancl rtranclp_into_tranclp1|drule (1) sees_method_fun|clarsimp)+
          done
      qed
    qed
  qed
next
  case (bisim1CallParams ps n ps' xs stk loc pc xcp obj M' v)
  note bisim2 = \<open>P,ps,h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)\<close>
  note bisim1 = \<open>P,obj,h \<turnstile> (obj, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note IH2 = bisim1CallParams.IH(2)
  note exec = \<open>exec_move_d P t (obj\<bullet>M'(ps)) h (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')\<close>
  note len = \<open>n + max_vars (Val v\<bullet>M'(ps')) \<le> length xs\<close>
  note bsok = \<open>bsok (obj\<bullet>M'(ps)) n\<close>
  from \<open>P,h \<turnstile> stk @ [v] [:\<le>] ST\<close> obtain T ST' where ST': "P,h \<turnstile> stk [:\<le>] ST'" and T: "typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>"
    by(auto simp add: list_all2_Cons1 list_all2_append1 conf_def)
  from bisim2 have pc: "pc \<le> length (compEs2 ps)" by(rule bisims1_pc_length_compEs2)
  show ?case
  proof(cases "pc < length (compEs2 ps)")
    case True
    from exec have "exec_meth_d (compP2 P) (compE2 (obj\<bullet>M'(ps))) (compxE2 (obj\<bullet>M'(ps)) 0 0) t h (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: exec_move_def)
    with True have exec': "exec_meth_d (compP2 P) (compEs2 ps) (stack_xlift (length [v]) (compxEs2 ps 0 0)) t h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 obj), xcp')"
      and pc': "pc' \<ge> length (compE2 obj)" by(safe dest!: Call_execParamD)
    from exec' bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_moves_d P t ps h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 obj), xcp')"
      by(unfold exec_moves_def)(drule (1) exec_meth_stk_splits, auto)
    with True have \<tau>: "\<tau>move2 (compP2 P) h (stk @ [v]) (obj\<bullet>M'(ps)) (length (compE2 obj) + pc) xcp = \<tau>moves2 (compP2 P) h stk ps pc xcp"
      by(auto simp add: \<tau>move2_iff \<tau>moves2_iff \<tau>instr_stk_drop_exec_moves)
    from IH2[OF exec'' _ _ ST' \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain es'' xs''
      where bisim': "P,ps,h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk'', loc', pc' - length (compE2 obj), xcp')"
      and red': "?reds ps' xs es'' xs'' ps stk pc (pc' - length (compE2 obj)) xcp xcp'" by auto
    from bisim' have "P,obj\<bullet>M'(ps),h' \<turnstile> (Val v\<bullet>M'(es''), xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 obj) + (pc' - length (compE2 obj)), xcp')"
      by(rule bisim1_bisims1.bisim1CallParams)
    moreover from True have "no_call2 (obj\<bullet>M'(ps)) (length (compE2 obj) + pc) = no_calls2 ps pc"
      by(simp add: no_calls2_def no_call2_def)
    moreover have "calls1 ps' = None \<Longrightarrow> call1 (Val v\<bullet>M'(ps')) = None \<or> is_vals ps'" by simp
    ultimately show ?thesis using red' \<tau> stk' pc pc'
      by(fastforce intro: Call1Params elim!: Call_\<tau>red1r_param Call_\<tau>red1t_param split: if_split_asm simp add: is_vals_conv)
  next
    case False
    with pc have [simp]: "pc = length (compEs2 ps)" by simp
    with bisim2 obtain vs where [simp]: "stk = rev vs" "xcp = None"
      and lenvs: "length vs = length ps" and vs: "is_vals ps' \<longrightarrow> ps' = map Val vs \<and> xs = loc"
      and call: "calls1 ps' = None"
      by(auto dest: bisims1_pc_length_compEs2D)
    with bisim2 len bsok have reds: "\<tau>reds1r P t h (ps', xs) (map Val vs, loc)"
      by(auto intro: bisims1_Val_\<tau>Reds1r simp add: bsok_def)
    from exec T lenvs 
    have "v = Null \<or> (is_Addr v \<and> (\<exists>T C' Ts' Tr' D'. typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor> \<and> class_type_of' T = \<lfloor>C'\<rfloor> \<and> P \<turnstile> C' sees M':Ts'\<rightarrow>Tr' = Native in D'))" (is "_ \<or> ?rest")
      by(fastforce elim!: exec_meth.cases simp add: is_Ref_def exec_move_def compP2_def has_method_def split: if_split_asm)
    thus ?thesis
    proof
      assume [simp]: "v = Null"
      hence \<tau>: "\<tau>move1 P h (Val v\<bullet>M'(map Val vs))"
        "\<tau>move2 (compP2 P) h (stk @ [v]) (obj\<bullet>M'(ps)) (length (compE2 obj) + length (compEs2 ps)) None"
        using lenvs by(auto simp add: \<tau>move2_iff)
      from lenvs
      have "P,obj\<bullet>M'(ps),h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 ps), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
        by(safe intro!: bisim1CallThrow) simp
      moreover have "True,P,t \<turnstile>1 \<langle>null\<bullet>M'(map Val vs),(h, loc)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer,(h, loc)\<rangle>"
        by(rule Red1CallNull)
      ultimately show ?thesis using exec pc \<tau> lenvs reds
        apply(auto elim!: exec_meth.cases simp add: exec_move_def) 
        apply(rule exI conjI|assumption)+
        apply(rule rtranclp.rtrancl_into_rtrancl)
        apply(erule Call_\<tau>red1r_param)
        by auto
    next
      assume ?rest
      then obtain a Ta C' Ts' Tr' D' where [simp]: "v = Addr a"
        and Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>"
        and iec: "P \<turnstile> class_type_of Ta sees M': Ts'\<rightarrow>Tr' = Native in D'" by auto
      with exec pc lenvs
      obtain ta' va h'' U Ts Ts' where redex: "(ta', va, h'') \<in> red_external_aggr (compP2 P) t a M' vs h"
        and ret: "(xcp', h', [(stk', loc', undefined, undefined, pc')]) = extRet2JVM (length vs) h'' (rev vs @ [Addr a]) loc undefined undefined (length (compE2 obj) + length (compEs2 ps)) [] va"
        and wtext': "P,h \<turnstile> a\<bullet>M'(vs) : U"
        and Ts: "map typeof\<^bsub>h\<^esub> vs = map Some Ts"
        and ta': "ta = extTA2JVM (compP2 P) ta'"
        by(fastforce simp add: is_Ref_def exec_move_def compP2_def external_WT'_iff exec_meth_instr confs_conv_map)
      have \<tau>: "\<tau>move1 P h (Val v\<bullet>M'(map Val vs)) \<longleftrightarrow> \<tau>move2 (compP2 P) h (stk @ [v]) (obj\<bullet>M'(ps)) (length (compE2 obj) + length (compEs2 ps)) None"
        using Ta iec lenvs
        by(auto simp add: \<tau>move2_iff map_eq_append_conv compP2_def)
      from ret have [simp]: "h'' = h'" by simp
      from wtext' have wtext'': "compP2 P,h \<turnstile> a\<bullet>M'(vs) : U" by(simp add: compP2_def external_WT'_iff)
      from wf have "wf_jvm_prog (compP2 P)" by(rule wt_compP2)
      then obtain wf_md where wf': "wf_prog wf_md (compP2 P)"
        unfolding wf_jvm_prog_def by(blast dest: wt_jvm_progD)
      from tconf have tconf': "compP2 P,h \<turnstile> t \<surd>t" by(simp add: compP2_def tconf_def)
      from redex have redex'': "compP2 P,t \<turnstile> \<langle>a\<bullet>M'(vs), h\<rangle> -ta'\<rightarrow>ext \<langle>va, h'\<rangle>"
        by(simp add: WT_red_external_list_conv[OF wf' wtext'' tconf', symmetric])
      hence redex': "P,t \<turnstile> \<langle>a\<bullet>M'(vs), h\<rangle> -ta'\<rightarrow>ext \<langle>va, h'\<rangle>" by(simp add: compP2_def)
      with Ta iec have "True,P,t \<turnstile>1 \<langle>addr a\<bullet>M'(map Val vs), (h, loc)\<rangle> -ta'\<rightarrow> \<langle>extRet2J (addr a\<bullet>M'(map Val vs)) va, (h', loc)\<rangle>"
        by -(rule Red1CallExternal, auto)
      moreover have "P,obj\<bullet>M'(ps),h' \<turnstile> (extRet2J (addr a\<bullet>M'(map Val vs)) va, loc) \<leftrightarrow> (stk', loc', pc', xcp')"
      proof(cases va)
        case (RetVal v)
        have "P,obj\<bullet>M'(ps),h' \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (obj\<bullet>M'(ps))), None)"
          by(rule bisim1Val2)(simp)
        with ret RetVal show ?thesis by simp
      next
        case (RetExc ad)
        from lenvs have "length ps = length (rev vs)" by simp
        hence "P,obj\<bullet>M'(ps),h' \<turnstile> (Throw ad, loc) \<leftrightarrow> (rev vs @ [v], loc, length (compE2 (obj)) + length (compEs2 ps), \<lfloor>ad\<rfloor>)"
          by(rule bisim1CallThrow)
        with ret RetExc show ?thesis by simp
      next
        case RetStaySame
        from lenvs have "length ps = length vs" by simp
        from bisims1_map_Val_append[OF bisims1Nil this, of P h' loc]
        have "P,ps,h' \<turnstile> (map Val vs, loc) [\<leftrightarrow>] (rev vs, loc, length (compEs2 ps), None)" by simp
        hence "P,obj\<bullet>M'(ps),h' \<turnstile> (addr a\<bullet>M'(map Val vs), loc) \<leftrightarrow> (rev vs @ [Addr a], loc, length (compE2 obj) + length (compEs2 ps), None)"
          by(rule bisim1_bisims1.bisim1CallParams)
        thus ?thesis using ret RetStaySame by simp
      qed
      moreover from \<open>preallocated h\<close> red_external_hext[OF redex'] have "preallocated h'" by(rule preallocated_hext) 
      from redex'' wtext'' \<open>hconf h\<close> have "hconf h'" by(rule external_call_hconf)
      with ta' redex' \<open>preallocated h'\<close>
      have "ta_bisim wbisim1 (extTA2J1 P ta') ta" by(auto intro: red_external_ta_bisim21[OF wf])
      moreover have "\<tau>move1 P h (Val v\<bullet>M'(map Val vs)) \<Longrightarrow> ta' = \<epsilon> \<and> h' = h"
        using Ta iec redex'
        by(fastforce dest: \<tau>external'_red_external_heap_unchanged \<tau>external'_red_external_TA_empty sees_method_fun simp add: \<tau>external'_def \<tau>external_def map_eq_append_conv)
      moreover from vs call have "call1 (Val v\<bullet>M'(ps')) \<noteq> None \<Longrightarrow> ps' = map Val vs \<and> loc = xs"
          by(auto split: if_split_asm simp add: is_vals_conv)
      ultimately show ?thesis using reds \<tau> pc Ta call
        apply(auto simp del: split_paired_Ex call1.simps calls1.simps split: if_split_asm simp add: map_eq_append_conv)
        apply(auto 4 4 simp del: split_paired_Ex call1.simps calls1.simps intro: rtranclp.rtrancl_into_rtrancl[OF Call_\<tau>red1r_param] rtranclp_into_tranclp1[OF Call_\<tau>red1r_param])[3]
        apply((assumption|rule exI conjI|erule Call_\<tau>red1r_param|simp add: map_eq_append_conv)+)
        done
    qed
  qed
next
  case (bisim1CallThrowObj obj n a xs stk loc pc ps M')
  note exec = \<open>?exec (obj\<bullet>M'(ps)) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,obj,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim1 have pc: "pc < length (compE2 obj)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 obj 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: exec_move_def match_ex_table_not_pcs_None)
  thus ?case ..
next
  case (bisim1CallThrowParams ps n vs a ps' xs stk loc pc obj M' v)
  note exec = \<open>?exec (obj\<bullet>M'(ps)) (stk @ [v]) loc (length (compE2 obj) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,ps,h \<turnstile> (map Val vs @ Throw a # ps', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim2 have pc: "pc < length (compEs2 ps)" by(auto dest: bisims1_ThrowD)
  from bisim2 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxEs2 ps 0 0) = None"
    unfolding compP2_def by(rule bisims1_xcp_Some_not_caught)
  with exec pc have False
    apply(auto elim!: exec_meth.cases simp add: compxEs2_size_convs compxEs2_stack_xlift_convs exec_move_def)
    apply(auto simp add: match_ex_table_append dest!: match_ex_table_shift_pcD match_ex_table_stack_xliftD match_ex_table_pc_length_compE2)
    done
  thus ?case ..
next
  case (bisim1CallThrow ps vs obj n M' a xs v)
  note lenvs = \<open>length ps = length vs\<close>
  note exec = \<open>?exec (obj\<bullet>M'(ps)) (vs @ [v]) xs (length (compE2 obj) + length (compEs2 ps)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  with lenvs have False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs exec_move_def dest!: match_ex_table_pc_length_compEs2)
  thus ?case ..
next
  case (bisim1BlockSome1 e n V Ty v xs)
  have "\<tau>move2 (compP2 P) h [] {V:Ty=\<lfloor>v\<rfloor>; e} 0 None" by(simp add: \<tau>move2_iff)
  with \<open>?exec {V:Ty=\<lfloor>v\<rfloor>; e} [] xs 0 None stk' loc' pc' xcp'\<close> \<open>P,e,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  show ?case by(fastforce elim!: exec_meth.cases intro: bisim1BlockSome2 simp add: exec_move_def)
next
  case (bisim1BlockSome2 e n V Ty v xs)
  have "\<tau>move2 (compP2 P) h [v] {V:Ty=\<lfloor>v\<rfloor>; e} (Suc 0) None" by(simp add: \<tau>move2_iff)
  with \<open>?exec {V:Ty=\<lfloor>v\<rfloor>; e} [v] xs (Suc 0) None stk' loc' pc' xcp'\<close> \<open>P,e,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  show ?case by(fastforce intro: r_into_rtranclp Block1Some bisim1BlockSome4[OF bisim1_refl] simp add: exec_move_def
                         elim!: exec_meth.cases)
next
  case (bisim1BlockSome4 e n  e' xs stk loc pc xcp V Ty v)
  note IH = bisim1BlockSome4.IH(2)
  note exec = \<open>?exec {V:Ty=\<lfloor>v\<rfloor>; e} stk loc (Suc (Suc pc)) xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bsok = \<open>bsok {V:Ty=\<lfloor>v\<rfloor>; e} n\<close>
  with \<open>n + max_vars {V:Ty=None; e'} \<le> length xs\<close>
  have V: "V < length xs" and len: "Suc n + max_vars e' \<le> length xs" and [simp]: "n = V" by simp_all
  let ?pre = "[Push v, Store V]"
  from exec have exec': "exec_meth_d (compP2 P) (?pre @ compE2 e) (shift (length ?pre) (compxE2 e 0 0)) t h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs exec_move_def)
  hence pc': "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_pc) auto
  hence pc'': "Suc (Suc (pc' - Suc (Suc 0))) = pc'" by simp
  moreover from exec' have "exec_move_d P t e h (stk, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
    unfolding exec_move_def by(rule exec_meth_drop) auto
  from IH[OF this len _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] bsok obtain e'' xs''
    where bisim': "P,e,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
    and red': "?red e' xs e'' xs'' e stk pc (pc' - length ?pre) xcp xcp'" by auto
  from bisim' have "P,{V:Ty=\<lfloor>v\<rfloor>; e},h' \<turnstile> ({V:Ty=None; e''}, xs'') \<leftrightarrow> (stk', loc', Suc (Suc (pc' - length ?pre)), xcp')"
    by(rule bisim1_bisims1.bisim1BlockSome4)
  moreover from pc' pc'' have "\<tau>move2 (compP2 P) h stk {V:Ty=\<lfloor>v\<rfloor>; e} (Suc (Suc pc)) xcp = \<tau>move2 (compP2 P) h stk e pc xcp" by(simp add: \<tau>move2_iff)
  moreover from red' have "length xs'' = length xs"
    by(auto split: if_split_asm dest!: \<tau>red1r_preserves_len \<tau>red1t_preserves_len red1_preserves_len)
  ultimately show ?case using red' pc'' V
    by(fastforce elim!: Block_None_\<tau>red1r_xt Block_None_\<tau>red1t_xt intro: Block1Red split: if_split_asm simp add: no_call2_def)
next
  case (bisim1BlockThrowSome e n a xs stk loc pc V Ty v)
  note exec = \<open>?exec {V:Ty=\<lfloor>v\<rfloor>; e} stk loc (Suc (Suc pc)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False 
    apply(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
    apply(auto simp only: compxE2_size_convs dest!: match_ex_table_shift_pcD)
    apply simp
    done
  thus ?case ..
next
  case (bisim1BlockNone e n e' xs stk loc pc xcp V Ty)
  note IH = bisim1BlockNone.IH(2)
  note exec = \<open>?exec {V:Ty=None; e} stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bsok = \<open>bsok {V:Ty=None; e} n\<close>
  with \<open>n + max_vars {V:Ty=None; e'} \<le> length xs\<close>
  have V: "V < length xs" and len: "Suc n + max_vars e' \<le> length xs" by simp_all
  have "\<tau>move2 (compP2 P) h stk {V:Ty=None; e} pc xcp = \<tau>move2 (compP2 P) h stk e pc xcp" by(simp add: \<tau>move2_iff)
  moreover
  from exec have "?exec e stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_BlockNone)
  from IH[OF this len _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] bsok obtain e'' xs''
    where bisim': "P,e,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
    and red': "?red e' xs e'' xs'' e stk pc pc' xcp xcp'" by auto
  from bisim' have "P,{V:Ty=None; e},h' \<turnstile> ({V:Ty=None; e''}, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
    by(rule bisim1_bisims1.bisim1BlockNone)
  ultimately show ?case using V red' 
    by(fastforce elim!: Block1Red Block_None_\<tau>red1r_xt Block_None_\<tau>red1t_xt simp add: no_call2_def)
next
  case (bisim1BlockThrowNone e n a xs stk loc pc V Ty)
  note exec = \<open>?exec {V:Ty=None; e} stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False by(auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1Sync1 e1 n e' xs stk loc pc xcp e2 V)
  note IH = bisim1Sync1.IH(2)
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e1,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note len = \<open>n + max_vars (sync\<^bsub>V\<^esub> (e') e2) \<le> length xs\<close>
  note bsok = \<open>bsok (sync\<^bsub>V\<^esub> (e1) e2) n\<close>
  from bisim have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    with exec have exec': "?exec e1 stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_Sync1)
    from True have "\<tau>move2 (compP2 P) h stk (sync\<^bsub>V\<^esub> (e1) e2) pc xcp = \<tau>move2 (compP2 P) h stk e1 pc xcp" by(simp add: \<tau>move2_iff)
    with IH[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] len bisim2 bsok show ?thesis
      by(fastforce intro: bisim1_bisims1.bisim1Sync1 Synchronized1Red1 elim!: Sync_\<tau>red1r_xt Sync_\<tau>red1t_xt simp add: no_call2_def)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e1)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (sync\<^bsub>V\<^esub> (e') e2, xs) (sync\<^bsub>V\<^esub> (Val v) e2, loc)" by(rule Sync_\<tau>red1r_xt)
    moreover have \<tau>: "\<tau>move2 (compP2 P) h [v] (sync\<^bsub>V\<^esub> (e1) e2) pc None" by(simp add: \<tau>move2_iff)
    moreover
    have "P,(sync\<^bsub>V\<^esub> (e1) e2),h \<turnstile> ((sync\<^bsub>V\<^esub> (Val v) e2), loc) \<leftrightarrow> ([v, v], loc, Suc (length (compE2 e1)), None)"
      by(rule bisim1Sync2)
    ultimately show ?thesis using exec stk xcp
      by(fastforce elim!: exec_meth.cases simp add: exec_move_def)
  qed
next
  case (bisim1Sync2 e1 n e2 V v xs)
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [v, v] xs (Suc (length (compE2 e1))) None stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e1,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  have "\<tau>move2 (compP2 P) h [v, v] (sync\<^bsub>V\<^esub> (e1) e2) (Suc (length (compE2 e1))) None" by(rule \<tau>move2Sync3)
  thus ?case using exec 
    by(fastforce elim!: exec_meth.cases intro: bisim1Sync3 simp add: exec_move_def)
next
  case (bisim1Sync3 e1 n e2 V v xs)
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [v] (xs[V := v]) (Suc (Suc (length (compE2 e1)))) None stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e1,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim2 = \<open>\<And>xs. P,e2,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note len = \<open>n + max_vars (sync\<^bsub>V\<^esub> (Val v) e2) \<le> length xs\<close>
  note bsok = \<open>bsok (sync\<^bsub>V\<^esub> (e1) e2) n\<close>
  with len have V: "V < length xs" by simp
  have \<tau>: "\<not> \<tau>move2 (compP2 P) h [v] (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None" by(simp add: \<tau>move2_iff)
  from exec have "(\<exists>a. v = Addr a \<and> stk' = [] \<and> loc' = xs[V := v] \<and> ta = \<lbrace>Lock\<rightarrow>a, SyncLock a\<rbrace> \<and> xcp' = None \<and> pc' = Suc (Suc (Suc (length (compE2 e1))))) \<or> (v = Null \<and> stk' = [v] \<and> loc' = xs[V := v] \<and> ta = \<epsilon> \<and> xcp' = \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> \<and> pc' = Suc (Suc (length (compE2 e1))))" (is "?c1 \<or> ?c2")
    by(fastforce elim!: exec_meth.cases simp add: is_Ref_def expand_finfun_eq fun_eq_iff finfun_upd_apply exec_move_def)
  thus ?case
  proof
    assume ?c1
    then obtain a where [simp]: "v = Addr a" "stk' = []" "loc' = xs[V := v]" "ta = \<lbrace>Lock\<rightarrow>a, SyncLock a\<rbrace>"
      "xcp' = None" "pc' = Suc (Suc (Suc (length (compE2 e1))))" by blast
    have "True,P,t \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (addr a) e2, (h, xs)\<rangle> -\<lbrace>Lock\<rightarrow>a, SyncLock a\<rbrace>\<rightarrow> \<langle>insync\<^bsub>V\<^esub> (a) e2,(h, xs[V := Addr a])\<rangle>"
      using V by(rule Lock1Synchronized)
    moreover from bisim2 have "P,sync\<^bsub>V\<^esub> (e1) e2,h \<turnstile> (insync\<^bsub>V\<^esub> (a) e2, xs[V := Addr a]) \<leftrightarrow> ([], xs[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)"
      by(auto intro: bisim1Sync4[where pc = 0, simplified])
    ultimately show ?case using exec \<tau>
      by(fastforce elim!: exec_meth.cases split: if_split_asm simp add: is_Ref_def exec_move_def ta_bisim_def ta_upd_simps)
  next
    assume ?c2
    hence [simp]: "v = Null" "stk' = [v]" "loc' = xs[V := v]" "ta = \<epsilon>" "xcp' = \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>"
      "pc' = Suc (Suc (length (compE2 e1)))" by simp_all
    from V have "True,P,t \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (null) e2, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer,(h, xs[V := Null])\<rangle>"
      by(rule Synchronized1Null)
    moreover 
    have "P,sync\<^bsub>V\<^esub> (e1) e2,h \<turnstile> (THROW NullPointer, xs[V := Null]) \<leftrightarrow> ([Null], xs[V := Null], Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1Sync11)
    ultimately show ?case using exec \<tau>
      by(fastforce elim!: exec_meth.cases split: if_split_asm simp add: is_Ref_def exec_move_def)
  qed
next
  case (bisim1Sync4 e2 n e' xs stk loc pc xcp e1 V a)
  note IH = bisim1Sync4.IH(2)
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) stk loc (Suc (Suc (Suc (length (compE2 e1) + pc)))) xcp stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars (insync\<^bsub>V\<^esub> (a) e') \<le> length xs\<close>
  note bsok = \<open>bsok (sync\<^bsub>V\<^esub> (e1) e2) n\<close>
  with len have V: "V < length xs" and len': "Suc n + max_vars e' \<le> length xs" by simp_all
  from bisim2 have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  let ?pre = "compE2 e1 @ [Dup, Store V, MEnter]"
  let ?post = "[Load V, MExit, Goto 4, Load V, MExit, ThrowExc]"
  from exec have exec': "exec_meth_d (compP2 P) (?pre @ compE2 e2 @ ?post)
    (compxE2 e1 0 0 @ shift (length ?pre) (compxE2 e2 0 0 @ [(0, length (compE2 e2), None, 3 + length (compE2 e2), 0)])) t
    h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: ac_simps eval_nat_numeral shift_compxE2 exec_move_def)
  hence pc': "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc[where n'=1]) auto
  from exec' have exec'': "exec_meth_d (compP2 P) (compE2 e2 @ ?post) 
    (compxE2 e2 0 0 @ [(0, length (compE2 e2), None, 3 + length (compE2 e2), 0)]) t
    h (stk, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
    by(rule exec_meth_drop_xt[where n=1]) auto
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    note pc = True
    hence \<tau>: "\<tau>move2 (compP2 P) h stk (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (Suc (length (compE2 e1) + pc)))) xcp = \<tau>move2 (compP2 P) h stk e2 pc xcp"
      by(simp add: \<tau>move2_iff)
    show ?thesis
    proof(cases "xcp = None \<or> (\<exists>a'. xcp = \<lfloor>a'\<rfloor> \<and> match_ex_table (compP2 P) (cname_of h a') pc (compxE2 e2 0 0) \<noteq> None)")
      case False
      then obtain a' where Some: "xcp = \<lfloor>a'\<rfloor>" 
        and True: "match_ex_table (compP2 P) (cname_of h a') pc (compxE2 e2 0 0) = None" by(auto simp del: not_None_eq)
      from Some \<open>conf_xcp' (compP2 P) h xcp\<close> obtain D
        where ha': "typeof_addr h a' = \<lfloor>Class_type D\<rfloor>" and subcls: "P \<turnstile> D \<preceq>\<^sup>* Throwable" by(auto simp add: compP2_def)
      from ha' subcls bisim2 True bsok have "\<tau>red1r P t h (e', xs) (Throw a', loc)"
        using len' unfolding Some compP2_def by(auto dest!: bisim1_xcp_\<tau>Red simp add: bsok_def)
      moreover from pc have "\<tau>move2 (compP2 P) h stk (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (Suc (pc + length (compE2 e1))))) \<lfloor>a'\<rfloor>"
        by(auto intro: \<tau>move2xcp)
      moreover 
      have "P, sync\<^bsub>V\<^esub> (e1) e2, h \<turnstile> (insync\<^bsub>V\<^esub> (a) Throw a', loc) \<leftrightarrow> ([Addr a'], loc, 6 + length (compE2 e1) + length (compE2 e2), None)"
        by(rule bisim1Sync7)
      ultimately show ?thesis using exec True pc Some ha' subcls
        apply(auto elim!: exec_meth.cases simp add: ac_simps eval_nat_numeral match_ex_table_append matches_ex_entry_def compP2_def exec_move_def)

        apply(simp_all only: compxE2_size_convs, auto dest: match_ex_table_shift_pcD match_ex_table_pc_length_compE2)
        apply(fastforce elim!: InSync_\<tau>red1r_xt)
        done
    next
      case True 
      with exec'' pc have "exec_meth_d (compP2 P) (compE2 e2 @ ?post) (compxE2 e2 0 0) t
        h (stk, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
        by(auto elim!: exec_meth.cases intro: exec_meth.intros simp add: match_ex_table_append exec_move_def)
      hence "exec_move_d P t e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
        using pc unfolding exec_move_def by(rule exec_meth_take)
      from IH[OF this len' _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] bsok obtain e'' xs''
        where bisim': "P,e2,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
        and red': "?red e' xs e'' xs'' e2 stk pc (pc' - length ?pre) xcp xcp'" by auto
      from bisim'
      have "P,sync\<^bsub>V\<^esub> (e1) e2, h' \<turnstile> (insync\<^bsub>V\<^esub> (a) e'', xs'') \<leftrightarrow> (stk', loc', Suc (Suc (Suc (length (compE2 e1) + (pc' - length ?pre)))), xcp')"
        by(rule bisim1_bisims1.bisim1Sync4)
      moreover from pc' have "Suc (Suc (Suc (length (compE2 e1) + (pc' - Suc (Suc (Suc (length (compE2 e1)))))))) = pc'"
        "Suc (Suc (Suc (pc' - Suc (Suc (Suc 0))))) = pc'"
        by simp_all
      ultimately show ?thesis using red' \<tau>
        by(fastforce intro: Synchronized1Red2 simp add: eval_nat_numeral no_call2_def elim!: InSync_\<tau>red1r_xt InSync_\<tau>red1t_xt split: if_split_asm)
    qed
  next
    case False
    with pc have [simp]: "pc = length (compE2 e2)" by simp
    with bisim2 obtain v where [simp]: "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    have "\<tau>move2 (compP2 P) h [v] (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (Suc (length (compE2 e1) + length (compE2 e2))))) None" by(simp add: \<tau>move2_iff)
    moreover from bisim2 pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro!: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (insync\<^bsub>V\<^esub> (a) e', xs) (insync\<^bsub>V\<^esub> (a) (Val v), loc)" by(rule InSync_\<tau>red1r_xt)
    moreover
    have "P,sync\<^bsub>V\<^esub> (e1) e2,h \<turnstile> (insync\<^bsub>V\<^esub> (a) (Val v), loc) \<leftrightarrow> ([loc ! V, v], loc, 4 + length (compE2 e1) + length (compE2 e2), None)"
      by(rule bisim1Sync5)
    ultimately show ?thesis using exec
      by(auto elim!: exec_meth.cases simp add: eval_nat_numeral exec_move_def) blast
  qed
next
  case (bisim1Sync5 e1 n e2 V a v xs)
  note bisim1 = \<open>P,e1,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [xs ! V, v] xs (4 + length (compE2 e1) + length (compE2 e2)) None stk' loc' pc' xcp'\<close>
  from \<open>n + max_vars (insync\<^bsub>V\<^esub> (a) Val v) \<le> length xs\<close> \<open>bsok (sync\<^bsub>V\<^esub> (e1) e2) n\<close> have V: "V < length xs" by simp
  have \<tau>: "\<not> \<tau>move2 (compP2 P) h [xs ! V, v] (sync\<^bsub>V\<^esub> (e1) e2) (4 + length (compE2 e1) + length (compE2 e2)) None"
    by(simp add: \<tau>move2_iff)
  have \<tau>': "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) Val v)" by auto
  from exec have "(\<exists>a'. xs ! V = Addr a') \<or> xs ! V = Null" (is "?c1 \<or> ?c2")
    by(auto elim!: exec_meth.cases simp add: split_beta is_Ref_def exec_move_def split: if_split_asm)
  thus ?case
  proof
    assume ?c1
    then obtain a' where xsV [simp]: "xs ! V = Addr a'" ..
    have "P,sync\<^bsub>V\<^esub> (e1) e2,h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, 5 + length (compE2 e1) + length (compE2 e2), None)"
      "P,sync\<^bsub>V\<^esub> (e1) e2,h \<turnstile> (THROW IllegalMonitorState,xs) \<leftrightarrow> ([Addr a', v],xs,4 + length (compE2 e1) + length (compE2 e2),\<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      by(rule bisim1Sync6, rule bisim1Sync12)
    moreover from xsV V have "True,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Val v, (h, xs)\<rangle> -\<lbrace>Unlock\<rightarrow>a', SyncUnlock a'\<rbrace>\<rightarrow> \<langle>Val v,(h, xs)\<rangle>"
      by(rule Unlock1Synchronized)
    moreover from xsV V have "True,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Val v, (h, xs)\<rangle> -\<lbrace>UnlockFail\<rightarrow>a'\<rbrace>\<rightarrow> \<langle>THROW IllegalMonitorState,(h, xs)\<rangle>"
      by(rule Unlock1SynchronizedFail[OF TrueI])
    ultimately show ?case using \<tau> \<tau>' exec
      by(fastforce elim!: exec_meth.cases simp add: is_Ref_def ta_bisim_def ac_simps exec_move_def ta_upd_simps)
  next
    assume xsV: "xs ! V = Null"
    have "P,sync\<^bsub>V\<^esub> (e1) e2,h \<turnstile> (THROW NullPointer,xs) \<leftrightarrow> ([Null, v],xs,4 + length (compE2 e1) + length (compE2 e2),\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1Sync12)
    thus ?case using \<tau> \<tau>' exec xsV V
      by(fastforce elim!: exec_meth.cases intro: Unlock1SynchronizedNull simp add: is_Ref_def ta_bisim_def ac_simps exec_move_def)
  qed
next
  case (bisim1Sync6 e1 n e2 V v x)
  note bisim1 = \<open>P,e1,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [v] x (5 + length (compE2 e1) + length (compE2 e2)) None stk' loc' pc' xcp'\<close>
  have "\<tau>move2 (compP2 P) h [v] (sync\<^bsub>V\<^esub> (e1) e2) (5 + length (compE2 e1) + length (compE2 e2)) None" by(simp add: \<tau>move2_iff)
  moreover
  have "P,sync\<^bsub>V\<^esub> (e1) e2,h \<turnstile> (Val v, x) \<leftrightarrow> ([v], x, length (compE2 (sync\<^bsub>V\<^esub> (e1) e2)), None)"
    by(rule bisim1Val2) simp
  moreover have "nat (9 + (int (length (compE2 e1)) + int (length (compE2 e2)))) = 9 + length (compE2 e1) + length (compE2 e2)" by arith
  ultimately show ?case using exec
    by(fastforce elim!: exec_meth.cases simp add: eval_nat_numeral exec_move_def)
next
  case (bisim1Sync7 e1 n e2 V a a' xs)
  note \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [Addr a'] xs (6 + length (compE2 e1) + length (compE2 e2)) None stk' loc' pc' xcp'\<close>
  moreover
  have "P,sync\<^bsub>V\<^esub> (e1) e2,h' \<turnstile> (insync\<^bsub>V\<^esub> (a) Throw a', xs) \<leftrightarrow>
        ([xs ! V, Addr a'], xs, 7 + length (compE2 e1) + length (compE2 e2), None)"
    by(rule bisim1Sync8)
  moreover have "\<tau>move2 (compP2 P) h [Addr a'] (sync\<^bsub>V\<^esub> (e1) e2) (6 + length (compE2 e1) + length (compE2 e2)) None"
    by(simp add: \<tau>move2_iff)
  ultimately show ?case by(fastforce elim!: exec_meth.cases simp add: eval_nat_numeral exec_move_def)
next
  case (bisim1Sync8 e1 n e2 V a a' xs)
  from \<open>n + max_vars (insync\<^bsub>V\<^esub> (a) Throw a') \<le> length xs\<close> \<open>bsok (sync\<^bsub>V\<^esub> (e1) e2) n\<close> have V: "V < length xs" by simp
  note \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [xs ! V, Addr a'] xs (7 + length (compE2 e1) + length (compE2 e2)) None stk' loc' pc' xcp'\<close>
  moreover have "\<not> \<tau>move2 (compP2 P) h [xs ! V, Addr a'] (sync\<^bsub>V\<^esub> (e1) e2) (7 + length (compE2 e1) + length (compE2 e2)) None"
    by(simp add: \<tau>move2_iff)
  moreover
  have "P,sync\<^bsub>V\<^esub> (e1) e2,h \<turnstile> (Throw a', xs) \<leftrightarrow> ([Addr a'], xs, 8 + length (compE2 e1) + length (compE2 e2), None)"
    "P,sync\<^bsub>V\<^esub> (e1) e2,h \<turnstile> (THROW IllegalMonitorState,xs) \<leftrightarrow> ([xs ! V, Addr a'],xs,7 + length (compE2 e1) + length (compE2 e2),\<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
    "P,sync\<^bsub>V\<^esub> (e1) e2,h \<turnstile> (THROW NullPointer,xs) \<leftrightarrow> ([Null, Addr a'],xs,7 + length (compE2 e1) + length (compE2 e2),\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
    by(rule bisim1Sync9 bisim1Sync14)+
  moreover {
    fix A
    assume "xs ! V = Addr A"
    hence "True,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw a',(h, xs)\<rangle> -\<lbrace>Unlock\<rightarrow>A, SyncUnlock A\<rbrace>\<rightarrow> \<langle>Throw a', (h, xs)\<rangle>"
      "True,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw a',(h, xs)\<rangle> -\<lbrace>UnlockFail\<rightarrow>A\<rbrace>\<rightarrow> \<langle>THROW IllegalMonitorState, (h, xs)\<rangle>"
      using V by(rule Synchronized1Throw2 Synchronized1Throw2Fail[OF TrueI])+ }
  moreover {
    assume "xs ! V = Null"
    hence "True,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw a',(h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h, xs)\<rangle>"
      using V by(rule Synchronized1Throw2Null) }
  moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) Throw a')" by fastforce
  ultimately show ?case
    by(fastforce elim!: exec_meth.cases simp add: eval_nat_numeral is_Ref_def ta_bisim_def ta_upd_simps exec_move_def split: if_split_asm)
next
  case (bisim1Sync9 e1 n e2 V a xs)
  note \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [Addr a] xs (8 + length (compE2 e1) + length (compE2 e2)) None stk' loc' pc' xcp'\<close>
  moreover
  have "P,sync\<^bsub>V\<^esub> (e1) e2,h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], xs, 8 + length (compE2 e1) + length (compE2 e2), \<lfloor>a\<rfloor>)"
    by(rule bisim1Sync10)
  moreover have "\<tau>move2 (compP2 P) h [Addr a] (sync\<^bsub>V\<^esub> (e1) e2) (8 + length (compE2 e1) + length (compE2 e2)) None"
    by(rule \<tau>move2Sync8)
  ultimately show ?case
    by(fastforce elim!: exec_meth.cases simp add: eval_nat_numeral exec_move_def split: if_split_asm)
next
  case (bisim1Sync10 e1 n e2 V a xs)
  from \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [Addr a] xs (8 + length (compE2 e1) + length (compE2 e2)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  have False by(auto elim!: exec_meth.cases simp add: matches_ex_entry_def match_ex_table_append_not_pcs exec_move_def)
  thus ?case ..
next
  case (bisim1Sync11 e1 n e2 V xs)
  from \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [Null] xs (Suc (Suc (length (compE2 e1)))) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'\<close>
  have False by(auto elim!: exec_meth.cases simp add: matches_ex_entry_def match_ex_table_append_not_pcs exec_move_def)
  thus ?case ..
next
  case (bisim1Sync12 e1 n e2 V a xs v v')
  from \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [v, v'] xs (4 + length (compE2 e1) + length (compE2 e2)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  have False by(auto elim!: exec_meth.cases simp add: matches_ex_entry_def match_ex_table_append_not_pcs exec_move_def)
  thus ?case ..
next
  case (bisim1Sync14 e1 n e2 V a xs v a')
  from \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) [v, Addr a'] xs (7 + length (compE2 e1) + length (compE2 e2)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  have False by(auto elim!: exec_meth.cases simp add: matches_ex_entry_def match_ex_table_append_not_pcs exec_move_def)
  thus ?case ..
next
  case bisim1InSync thus ?case by simp
next
  case (bisim1SyncThrow e1 n a xs stk loc pc e2 V)
  note exec = \<open>?exec (sync\<^bsub>V\<^esub> (e1) e2) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim1 have pc: "pc < length (compE2 e1)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e1 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False
    apply(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs exec_move_def)
    apply(auto dest!: match_ex_table_shift_pcD simp add: matches_ex_entry_def)
    done
  thus ?case ..
next
  case (bisim1Seq1 e1 n e' xs stk loc pc xcp e2)
  note IH = bisim1Seq1.IH(2)
  note exec = \<open>?exec (e1;; e2) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e1,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars (e';;e2) \<le> length xs\<close>
  note bsok = \<open>bsok (e1;; e2) n\<close>
  from bisim have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    let ?post = "Pop # compE2 e2"
    from exec have exec': "?exec e1 stk loc pc xcp stk' loc' pc' xcp'" using True by(simp add: exec_move_Seq1)
    from True have "\<tau>move2 (compP2 P) h stk (e1;;e2) pc xcp = \<tau>move2 (compP2 P) h stk e1 pc xcp" by(simp add: \<tau>move2_iff)
    with IH[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok show ?thesis
      by(fastforce intro: bisim1_bisims1.bisim1Seq1 Seq1Red elim!: Seq_\<tau>red1r_xt Seq_\<tau>red1t_xt simp add: no_call2_def)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e1)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (e';; e2, xs) (Val v;;e2, loc)" by(rule Seq_\<tau>red1r_xt)
    also have "\<tau>move1 P h (Val v;;e2)" by(rule \<tau>move1SeqRed)
    hence "\<tau>red1r P t h (Val v;;e2, loc) (e2, loc)" by(auto intro: Red1Seq r_into_rtranclp)
    also have \<tau>: "\<tau>move2 (compP2 P) h [v] (e1;;e2) pc None" by(simp add: \<tau>move2_iff)
    moreover from \<open>P,e2,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, 0, None)\<close>
    have "P,e1;;e2,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 e1) + 0), None)"
      by(rule bisim1Seq2)
    ultimately show ?thesis using exec stk xcp
      by(fastforce elim!: exec_meth.cases simp add: exec_move_def)
  qed
next
  case (bisim1SeqThrow1 e1 n a xs stk loc pc e2)
  note exec = \<open>?exec (e1;;e2) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e1,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim1 have pc: "pc < length (compE2 e1)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e1 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
  thus ?case ..
next
  case (bisim1Seq2 e2 n e' xs stk loc pc xcp e1)
  note IH = bisim1Seq2.IH(2)
  note bisim1 = \<open>\<And>xs. P,e1,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars e' \<le> length xs\<close>
  note exec = \<open>?exec (e1;; e2) stk loc (Suc (length (compE2 e1) + pc)) xcp stk' loc' pc' xcp'\<close>
  note bsok = \<open>bsok (e1;; e2) n\<close>
  let ?pre = "compE2 e1 @ [Pop]"
  from exec have exec': "exec_meth_d (compP2 P) (?pre @ compE2 e2) (compxE2 e1 0 0 @ shift (length ?pre) (compxE2 e2 0 0)) t h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 exec_move_def)
  hence "?exec e2 stk loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
    unfolding exec_move_def by(rule exec_meth_drop_xt, auto)
  from IH[OF this len _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] bsok obtain e'' xs''
    where bisim': "P,e2,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
    and red: "?red e' xs e'' xs'' e2 stk pc (pc' - length ?pre) xcp xcp'" by auto
  from bisim' 
  have "P,e1;;e2,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', Suc (length (compE2 e1) + (pc' - length ?pre)), xcp')"
    by(rule bisim1_bisims1.bisim1Seq2)
  moreover have \<tau>: "\<tau>move2 (compP2 P) h stk (e1;;e2) (Suc (length (compE2 e1) + pc)) xcp = \<tau>move2 (compP2 P) h stk e2 pc xcp"
    by(simp add: \<tau>move2_iff)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc) auto
  ultimately show ?case using red by(fastforce split: if_split_asm simp add: no_call2_def)
next
  case (bisim1Cond1 e n e' xs stk loc pc xcp e1 e2)
  note IH = bisim1Cond1.IH(2)
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim1 = \<open>\<And>xs. P,e1,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim2 = \<open>\<And>xs. P,e2,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  from \<open>n + max_vars (if (e') e1 else e2) \<le> length xs\<close>
  have len: "n + max_vars e' \<le> length xs" by simp
  note exec = \<open>?exec (if (e) e1 else e2) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bsok = \<open>bsok (if (e) e1 else e2) n\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    let ?post = "IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2"
    from exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'" using True
      by(simp add: exec_move_Cond1)
    from True have "\<tau>move2 (compP2 P) h stk (if (e) e1 else e2) pc xcp = \<tau>move2 (compP2 P) h stk e pc xcp"
      by(simp add: \<tau>move2_iff)
    with IH[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok show ?thesis
      by(fastforce intro: bisim1_bisims1.bisim1Cond1 Cond1Red elim!: Cond_\<tau>red1r_xt Cond_\<tau>red1t_xt simp add: no_call2_def)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (if (e') e1 else e2, xs) (if (Val v) e1 else e2, loc)" by(rule Cond_\<tau>red1r_xt)
    moreover have "\<tau>move1 P h (if (Val v) e1 else e2)" by(rule \<tau>move1CondRed)
    moreover have \<tau>: "\<tau>move2 (compP2 P) h [v] (if (e) e1 else e2) pc None" by(simp add: \<tau>move2_iff)
    moreover from bisim1[of loc]
    have "P,if (e) e1 else e2,h \<turnstile> (e1, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 e) + 0), None)"
      by(rule bisim1CondThen)
    moreover from bisim2[of loc]
    have "P,if (e) e1 else e2,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, Suc (Suc (length (compE2 e) + length (compE2 e1) + 0)), None)"
      by(rule bisim1CondElse)
    moreover have "nat (int (length (compE2 e)) + (2 + int (length (compE2 e1)))) = Suc (Suc (length (compE2 e) + length (compE2 e1) + 0))" by simp
    moreover from exec xcp stk have "typeof\<^bsub>h\<^esub> v = \<lfloor>Boolean\<rfloor>" by(auto simp add: exec_move_def exec_meth_instr)
    ultimately show ?thesis using exec stk xcp
      by(fastforce elim!: exec_meth.cases intro: Red1CondT Red1CondF elim!: rtranclp.rtrancl_into_rtrancl simp add: eval_nat_numeral exec_move_def)
  qed
next
  case (bisim1CondThen e1 n e' xs stk loc pc xcp e e2)
  note IH = bisim1CondThen.IH(2)
  note bisim1 = \<open>P,e1,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim = \<open>\<And>xs. P,e,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim2 = \<open>\<And>xs. P,e2,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note len = \<open>n + max_vars e' \<le> length xs\<close>
  note exec = \<open>?exec (if (e) e1 else e2) stk loc (Suc (length (compE2 e) + pc)) xcp stk' loc' pc' xcp'\<close>
  note bsok = \<open>bsok (if (e) e1 else e2) n\<close>
  from bisim1 have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    let ?pre = "compE2 e @ [IfFalse (2 + int (length (compE2 e1)))]"
    let ?post = "Goto (1 + int (length (compE2 e2))) # compE2 e2"
    from exec have exec': "exec_meth_d (compP2 P) (?pre @ compE2 e1 @ ?post)
      (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 (Suc 0) 0))) t
      h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 ac_simps exec_move_def)
    hence "exec_meth_d (compP2 P) (compE2 e1 @ ?post) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 (Suc 0) 0)) t
      h (stk, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_move_d P t e1 h (stk, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
      using True unfolding exec_move_def by(rule exec_meth_take_xt)
    from IH[OF this len _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] bsok obtain e'' xs''
      where bisim': "P,e1,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
      and red: "?red e' xs e'' xs'' e1 stk pc (pc' - length ?pre) xcp xcp'" by auto
    from bisim' 
    have "P,if (e) e1 else e2,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', Suc (length (compE2 e) + (pc' - length ?pre)), xcp')"
      by(rule bisim1_bisims1.bisim1CondThen)
    moreover from True have \<tau>: "\<tau>move2 (compP2 P) h stk (if (e) e1 else e2) (Suc (length (compE2 e) + pc)) xcp = \<tau>move2 (compP2 P) h stk e1 pc xcp"
      by(simp add: \<tau>move2_iff)
    moreover from exec' have "pc' \<ge> length ?pre"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using red by(fastforce split: if_split_asm simp add: no_call2_def)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e1)" by simp
    with bisim1 obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    moreover have \<tau>: "\<tau>move2 (compP2 P) h [v] (if (e) e1 else e2) (Suc (length (compE2 e) + length (compE2 e1))) None"
      by(simp add: \<tau>move2_iff)
    moreover
    have "P,if (e) e1 else e2,h \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (if (e) e1 else e2)), None)"
      by(rule bisim1Val2) simp
    moreover have "nat (2 + (int (length (compE2 e)) + (int (length (compE2 e1)) + int (length (compE2 e2))))) = length (compE2 (if (e) e1 else e2))" by simp
    ultimately show ?thesis using exec xcp stk by(fastforce elim!: exec_meth.cases simp add: exec_move_def)
  qed
next
  case (bisim1CondElse e2 n e' xs stk loc pc xcp e e1)
  note IH = bisim1CondElse.IH(2)
  note bisim2 = \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim = \<open>\<And>xs. P,e,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim1 = \<open>\<And>xs. P,e1,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note len = \<open>n + max_vars e' \<le> length xs\<close>
  note exec = \<open>?exec (if (e) e1 else e2) stk loc (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))) xcp stk' loc' pc' xcp'\<close>
  note bsok = \<open>bsok (if (e) e1 else e2) n\<close>
  let ?pre = "compE2 e @ IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ [Goto (1 + int (length (compE2 e2)))]"
  from exec have exec': "exec_meth_d (compP2 P) (?pre @ compE2 e2)
    ((compxE2 e 0 0 @ compxE2 e1 (Suc (length (compE2 e))) 0) @ shift (length ?pre) (compxE2 e2 0 0)) t
    h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 ac_simps exec_move_def)
  hence "?exec e2 stk loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
    unfolding exec_move_def by(rule exec_meth_drop_xt) auto
  from IH[OF this len _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] bsok obtain e'' xs''
    where bisim': "P,e2,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
    and red: "?red e' xs e'' xs'' e2 stk pc (pc' - length ?pre) xcp xcp'" by auto
  from bisim'
  have "P,if (e) e1 else e2,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', Suc (Suc (length (compE2 e) + length (compE2 e1) + (pc' - length ?pre))), xcp')"
    by(rule bisim1_bisims1.bisim1CondElse)
  moreover have \<tau>: "\<tau>move2 (compP2 P) h stk (if (e) e1 else e2) (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))) xcp = \<tau>move2 (compP2 P) h stk e2 pc xcp"
    by(simp add: \<tau>move2_iff)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc) auto
  moreover hence "Suc (Suc (pc' - Suc (Suc 0))) = pc'" by simp
  ultimately show ?case using red by(fastforce simp add: eval_nat_numeral no_call2_def split: if_split_asm)
next
  case (bisim1CondThrow e n a xs stk loc pc e1 e2)
  note exec = \<open>?exec (if (e) e1 else e2) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
  thus ?case ..
next
  case (bisim1While1 c n e xs)
  note IH = bisim1While1.IH(2)
  note bisim = \<open>\<And>xs. P,c,h \<turnstile> (c, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim1 = \<open>\<And>xs. P,e,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  from \<open>n + max_vars (while (c) e) \<le> length xs\<close>
  have len: "n + max_vars c \<le> length xs" by simp
  note exec = \<open>?exec (while (c) e) [] xs 0 None stk' loc' pc' xcp'\<close>
  note bsok = \<open>bsok (while (c) e) n\<close>
  let ?post = "IfFalse (int (length (compE2 e)) + 3) # compE2 e @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit]"
  from exec have "?exec c [] xs 0 None stk' loc' pc' xcp'" by(simp add: exec_move_While1)
  from IH[OF this len] bsok obtain e'' xs''
    where bisim': "P,c,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
    and red: "?red c xs e'' xs'' c [] 0 pc' None xcp'" by fastforce
  from bisim'
  have "P,while (c) e,h' \<turnstile> (if (e'') (e;;while(c) e) else unit, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
    by(rule bisim1While3)
  moreover have "True,P,t \<turnstile>1 \<langle>while (c) e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>if (c) (e;;while (c) e) else unit, (h, xs)\<rangle>"
    by(rule Red1While)
  hence "\<tau>red1r P t h (while (c) e, xs) (if (c) (e;;while (c) e) else unit, xs)"
    by(auto intro: r_into_rtranclp \<tau>move1WhileRed)
  moreover have "\<tau>move2 (compP2 P) h [] (while (c) e) 0 None = \<tau>move2 (compP2 P) h [] c 0 None" by(simp add: \<tau>move2_iff)
  ultimately show ?case using red
    by(fastforce elim!: rtranclp_trans rtranclp_tranclp_tranclp intro: Cond1Red elim!: Cond_\<tau>red1r_xt Cond_\<tau>red1t_xt simp add: no_call2_def)
next
  case (bisim1While3 c n e' xs stk loc pc xcp e)
  note IH = bisim1While3.IH(2)
  note bisim = \<open>P,c,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim1 = \<open>\<And>xs. P,e,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  from \<open>n + max_vars (if (e') (e;;while (c) e) else unit) \<le> length xs\<close>
  have len: "n + max_vars e' \<le> length xs" by simp
  note bsok = \<open>bsok (while (c) e) n\<close>
  note exec = \<open>?exec (while (c) e) stk loc pc xcp stk' loc' pc' xcp'\<close>
  from bisim have pc: "pc \<le> length (compE2 c)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 c)")
    case True
    let ?post = "IfFalse (int (length (compE2 e)) + 3) # compE2 e @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit]"
    from exec have "exec_meth_d (compP2 P) (compE2 c @ ?post) (compxE2 c 0 0 @ shift (length (compE2 c)) (compxE2 e (Suc 0) 0)) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 exec_move_def)
    hence "?exec c stk loc pc xcp stk' loc' pc' xcp'"
      using True unfolding exec_move_def by(rule exec_meth_take_xt)
    from IH[OF this len _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] bsok obtain e'' xs''
      where bisim': "P,c,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red e' xs e'' xs'' c stk pc pc' xcp xcp'" by auto
    from bisim'
    have "P,while (c) e,h' \<turnstile> (if (e'') (e;;while(c) e) else unit, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(rule bisim1_bisims1.bisim1While3)
    moreover have "\<tau>move2 (compP2 P) h stk (while (c) e) pc xcp = \<tau>move2 (compP2 P) h stk c pc xcp" using True
      by(simp add: \<tau>move2_iff)
    ultimately show ?thesis using red
      by(fastforce elim!: rtranclp_trans intro: Cond1Red elim!: Cond_\<tau>red1r_xt Cond_\<tau>red1t_xt simp add: no_call2_def)
  next
    case False
    with pc have [simp]: "pc = length (compE2 c)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len bsok  have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (if (e') (e;; while (c) e) else unit, xs) (if (Val v) (e;; while (c) e) else unit, loc)"
      by(rule Cond_\<tau>red1r_xt)
    moreover have \<tau>: "\<tau>move2 (compP2 P) h [v] (while (c) e) (length (compE2 c)) None" by(simp add: \<tau>move2_iff)
    moreover have "\<tau>move1 P h (if (Val v) (e;;while (c) e) else unit)" by(rule \<tau>move1CondRed)
    moreover from bisim1[of loc]
    have "P,while (c) e,h \<turnstile> (e;;while(c) e, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 c) + 0), None)"
      by(rule bisim1While4)
    moreover
    have "P,while (c) e,h \<turnstile> (unit, loc) \<leftrightarrow> ([], loc, Suc (Suc (Suc (length (compE2 c) + length (compE2 e)))), None)"
      by(rule bisim1While7)
    moreover from exec stk xcp have "typeof\<^bsub>h\<^esub> v = \<lfloor>Boolean\<rfloor>"
      by(auto simp add: exec_meth_instr exec_move_def)
    moreover have "nat (int (length (compE2 c)) + (3 + int (length (compE2 e)))) = Suc (Suc (Suc (length (compE2 c) + length (compE2 e))))" by simp
    ultimately show ?thesis using exec stk xcp
      by(fastforce elim!: exec_meth.cases rtranclp_trans intro: Red1CondT Red1CondF simp add: eval_nat_numeral exec_move_def)
  qed
next
  case (bisim1While4 e n e' xs stk loc pc xcp c)
  note IH = bisim1While4.IH(2)
  note bisim = \<open>\<And>xs. P,c,h \<turnstile> (c, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  from \<open>n + max_vars (e';; while (c) e) \<le> length xs\<close>
  have len: "n + max_vars e' \<le> length xs" by simp
  note exec = \<open>?exec (while (c) e) stk loc (Suc (length (compE2 c) + pc)) xcp stk' loc' pc' xcp'\<close>
  note bsok = \<open>bsok (while (c) e) n\<close>
  from bisim1 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    let ?pre = "compE2 c @ [IfFalse (int (length (compE2 e)) + 3)]"
    let ?post = "[Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit]"
    from exec have "exec_meth_d (compP2 P) ((?pre @ compE2 e) @ ?post) (compxE2 c 0 0 @ shift (length ?pre) (compxE2 e 0 0)) t h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 exec_move_def)
    hence exec': "exec_meth_d (compP2 P) (?pre @ compE2 e) (compxE2 c 0 0 @ shift (length ?pre) (compxE2 e 0 0)) t h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(rule exec_meth_take)(simp add: True)
    hence "?exec e stk loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
      unfolding exec_move_def by(rule exec_meth_drop_xt) auto
    from IH[OF this len _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] bsok obtain e'' xs''
      where bisim': "P,e,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
      and red: "?red e' xs e'' xs'' e stk pc (pc' - length ?pre) xcp xcp'" by auto
    from red have "?red (e';;while (c) e) xs (e'';;while (c) e) xs'' e stk pc (pc' - length ?pre) xcp xcp'"
      by(fastforce intro: Seq1Red elim!: Seq_\<tau>red1r_xt Seq_\<tau>red1t_xt split: if_split_asm)
    moreover from bisim'
    have "P,while (c) e,h' \<turnstile> (e'';;while(c) e, xs'') \<leftrightarrow> (stk', loc', Suc (length (compE2 c) + (pc' - length ?pre)), xcp')"
      by(rule bisim1_bisims1.bisim1While4)
    moreover have "\<tau>move2 (compP2 P) h stk (while (c) e) (Suc (length (compE2 c) + pc)) xcp = \<tau>move2 (compP2 P) h stk e pc xcp"
      using True by(simp add: \<tau>move2_iff)
    moreover from exec' have "pc' \<ge> length ?pre"
      by(rule exec_meth_drop_xt_pc) auto
    moreover have "no_call2 e pc \<Longrightarrow> no_call2 (while (c) e) (Suc (length (compE2 c) + pc))"
      by(simp add: no_call2_def)
    ultimately show ?thesis
      apply(auto split: if_split_asm)
      apply(fastforce+)[6]
      apply(rule exI conjI|assumption|rule rtranclp.rtrancl_refl|simp)+
      done
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim1 obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (e';; while (c) e, xs) (Val v;; while (c) e, loc)" by(rule Seq_\<tau>red1r_xt)
    moreover have \<tau>: "\<tau>move2 (compP2 P) h [v] (while (c) e) (Suc (length (compE2 c) + length (compE2 e))) None"
      by(simp add: \<tau>move2_iff)
    moreover have "\<tau>move1 P h (Val v;;while (c) e)" by(rule \<tau>move1SeqRed)
    moreover
    have "P,while (c) e,h \<turnstile> (while(c) e, loc) \<leftrightarrow> ([], loc, Suc (Suc (length (compE2 c) + length (compE2 e))), None)"
      by(rule bisim1While6)
    ultimately show ?thesis using exec stk xcp
      by(fastforce elim!: exec_meth.cases rtranclp_trans intro: Red1Seq simp add: eval_nat_numeral exec_move_def)
  qed
next
  case (bisim1While6 c n e xs)
  note exec = \<open>?exec (while (c) e) [] xs (Suc (Suc (length (compE2 c) + length (compE2 e)))) None stk' loc' pc' xcp'\<close>
  moreover have "\<tau>move2 (compP2 P) h [] (while (c) e) (Suc (Suc (length (compE2 c) + length (compE2 e)))) None"
    by(simp add: \<tau>move2_iff)
  moreover
  have "P,while (c) e,h' \<turnstile> (if (c) (e;; while (c) e) else unit, xs) \<leftrightarrow> ([], xs, 0, None)"
    by(rule bisim1While3[OF bisim1_refl])
  moreover have "\<tau>red1t P t h (while (c) e, xs) (if (c) (e;; while (c) e) else unit, xs)"
    by(rule tranclp.r_into_trancl)(auto intro: Red1While)
  ultimately show ?case
    by(fastforce elim!: exec_meth.cases simp add: exec_move_def)
next
  case (bisim1While7 c n e xs)
  note \<open>?exec (while (c) e) [] xs (Suc (Suc (Suc (length (compE2 c) + length (compE2 e))))) None stk' loc' pc' xcp'\<close>
  moreover have "\<tau>move2 (compP2 P) h [] (while (c) e) (Suc (Suc (Suc (length (compE2 c) + length (compE2 e))))) None"
    by(simp add: \<tau>move2_iff)
  moreover have "P,while (c) e,h' \<turnstile> (unit, xs) \<leftrightarrow> ([Unit], xs, length (compE2 (while (c) e)), None)"
    by(rule bisim1Val2) simp
  ultimately show ?case by(fastforce elim!: exec_meth.cases simp add: exec_move_def)
next
  case (bisim1WhileThrow1 c n a xs stk loc pc e)
  note exec = \<open>?exec (while (c) e) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,c,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim1 have pc: "pc < length (compE2 c)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 c 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
  thus ?case ..
next
  case (bisim1WhileThrow2 e n a xs stk loc pc c)
  note exec = \<open>?exec (while (c) e) stk loc (Suc (length (compE2 c) + pc)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False
    apply(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
    apply(auto dest!: match_ex_table_shift_pcD simp only: compxE2_size_convs)
    apply simp
    done
  thus ?case ..
next
  case (bisim1Throw1 e n e' xs stk loc pc xcp)
  note IH = bisim1Throw1.IH(2)
  note exec = \<open>?exec (throw e) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_vars (throw e') \<le> length xs\<close>
  note bsok = \<open>bsok (throw e) n\<close>
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_Throw)
    from True have "\<tau>move2 (compP2 P) h stk (throw e) pc xcp = \<tau>move2 (compP2 P) h stk e pc xcp" by(simp add: \<tau>move2_iff)
    with IH[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok show ?thesis
      by(fastforce intro: bisim1_bisims1.bisim1Throw1 Throw1Red elim!: Throw_\<tau>red1r_xt Throw_\<tau>red1t_xt simp add: no_call2_def)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (throw e', xs) (throw (Val v), loc)" by(rule Throw_\<tau>red1r_xt)
    moreover have \<tau>: "\<tau>move2 (compP2 P) h [v] (throw e) pc None" by(simp add: \<tau>move2_iff)
    moreover 
    have "\<And>a. P,throw e,h \<turnstile> (Throw a, loc) \<leftrightarrow> ([Addr a], loc, length (compE2 e), \<lfloor>a\<rfloor>)"
      by(rule bisim1Throw2)
    moreover
    have "P,throw e,h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([Null], loc, length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1ThrowNull)
    moreover from exec stk xcp \<open>P,h \<turnstile> stk [:\<le>] ST\<close> obtain T' where T': "typeof\<^bsub>h\<^esub> v = \<lfloor>T'\<rfloor>" "P \<turnstile> T' \<le> Class Throwable"
      by(auto simp add: exec_move_def exec_meth_instr list_all2_Cons1 conf_def compP2_def)
    moreover with T' have "v \<noteq> Null \<Longrightarrow> \<exists>C. T' = Class C" by(cases T')(auto dest: Array_widen)
    moreover have "\<tau>red1r P t h (throw null, loc) (THROW NullPointer, loc)"
      by(auto intro: r_into_rtranclp Red1ThrowNull \<tau>move1ThrowNull)
    ultimately show ?thesis using exec stk xcp T' unfolding exec_move_def
      by(cases v)(fastforce elim!: exec_meth.cases intro: rtranclp_trans)+
  qed
next
  case (bisim1Throw2 e n a xs)
  note exec = \<open>?exec (throw e) [Addr a] xs (length (compE2 e)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  hence False by(auto elim!: exec_meth.cases dest: match_ex_table_pc_length_compE2 simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1ThrowNull e n xs)
  note exec = \<open>?exec (throw e) [Null] xs (length (compE2 e)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'\<close>
  hence False by(auto elim!: exec_meth.cases dest: match_ex_table_pc_length_compE2 simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1ThrowThrow e n a xs stk loc pc)
  note exec = \<open>?exec (throw e) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim1 have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False by(auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1Try e n e' xs stk loc pc xcp e2 C' V)
  note IH = bisim1Try.IH(2)
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim1 = \<open>\<And>xs. P,e2,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note exec = \<open>?exec (try e catch(C' V) e2) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bsok = \<open>bsok (try e catch(C' V) e2) n\<close>
  with \<open>n + max_vars (try e' catch(C' V) e2) \<le> length xs\<close>
  have len: "n + max_vars e' \<le> length xs" and V: "V < length xs" by simp_all
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    note pc = True
    show ?thesis
    proof(cases "xcp = None \<or> (\<exists>a'. xcp = \<lfloor>a'\<rfloor> \<and> match_ex_table (compP2 P) (cname_of h a') pc (compxE2 e 0 0) \<noteq> None)")
      case False
      then obtain a' where Some: "xcp = \<lfloor>a'\<rfloor>" 
        and True: "match_ex_table (compP2 P) (cname_of h a') pc (compxE2 e 0 0) = None" by(auto simp del: not_None_eq)
      from Some bisim \<open>conf_xcp' (compP2 P) h xcp\<close> have "\<exists>C. typeof\<^bsub>h\<^esub> (Addr a') = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable"
        by(auto simp add: compP2_def)
      then obtain C'' where ha': "typeof_addr h a' = \<lfloor>Class_type C''\<rfloor>" 
        and subclsThrow: "P \<turnstile> C'' \<preceq>\<^sup>* Throwable" by(auto)
      with exec True Some pc have subcls: "P \<turnstile> C'' \<preceq>\<^sup>* C'"
        apply(auto elim!: exec_meth.cases simp add: match_ex_table_append compP2_def matches_ex_entry_def exec_move_def cname_of_def split: if_split_asm)
        apply(simp only: compxE2_size_convs, simp)
        done
      moreover from ha' subclsThrow bsok have red: "\<tau>red1r P t h (e', xs) (Throw a', loc)"
        and bisim': "P,e,h \<turnstile> (Throw a', loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)" using bisim True len
        unfolding Some compP2_def by(auto dest!: bisim1_xcp_\<tau>Red simp add: bsok_def)
      from red have lenloc: "length loc = length xs" by(rule \<tau>red1r_preserves_len)
      from red have "\<tau>red1r P t h (try e' catch(C' V) e2, xs) (try (Throw a') catch(C' V) e2, loc)"
        by(rule Try_\<tau>red1r_xt)
      hence "\<tau>red1r P t h (try e' catch(C' V) e2, xs) ({V:Class C'=None; e2}, loc[V := Addr a'])"
        using ha' subcls V unfolding lenloc[symmetric]
        by(auto intro: rtranclp.rtrancl_into_rtrancl Red1TryCatch \<tau>move1TryThrow)
      moreover from pc have "\<tau>move2 (compP2 P) h stk (try e catch(C' V) e2) pc \<lfloor>a'\<rfloor>" by(simp add: \<tau>move2_iff)
      moreover from bisim' ha' subcls
      have "P,try e catch(C' V) e2,h \<turnstile> ({V:Class C'=None; e2}, loc[V := Addr a']) \<leftrightarrow> ([Addr a'], loc, Suc (length (compE2 e)), None)"
        by(rule bisim1TryCatch1)
      ultimately show ?thesis using exec True pc Some ha' subclsThrow
        apply(auto elim!: exec_meth.cases simp add: ac_simps eval_nat_numeral match_ex_table_append matches_ex_entry_def compP2_def exec_move_def cname_of_def)
        apply fastforce
        apply(simp_all only: compxE2_size_convs, auto dest: match_ex_table_shift_pcD)
        done
    next
      case True
      let ?post = "Goto (int (length (compE2 e2)) + 2) # Store V # compE2 e2"
      from exec True have "exec_meth_d (compP2 P) (compE2 e @ ?post) (compxE2 e 0 0 @ shift (length (compE2 e)) (compxE2 e2 (Suc (Suc 0)) 0)) t h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
        by(auto elim!: exec_meth.cases intro: exec_meth.intros simp add: match_ex_table_append shift_compxE2 exec_move_def)
      hence "?exec e stk loc pc xcp stk' loc' pc' xcp'"
        using pc unfolding exec_move_def by(rule exec_meth_take_xt)
      from IH[OF this len _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] bsok obtain e'' xs''
        where bisim': "P,e,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
        and red': "?red e' xs e'' xs'' e stk pc pc' xcp xcp'" by auto
      from bisim'
      have "P,try e catch(C' V) e2,h' \<turnstile> (try e'' catch(C' V) e2, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
        by(rule bisim1_bisims1.bisim1Try)
      moreover from pc have "\<tau>move2 (compP2 P) h stk (try e catch(C' V) e2) pc xcp = \<tau>move2 (compP2 P) h stk e pc xcp"
        by(simp add: \<tau>move2_iff)
      ultimately show ?thesis using red' by(fastforce intro: Try1Red elim!: Try_\<tau>red1r_xt Try_\<tau>red1t_xt simp add: no_call2_def)
    qed
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>red1r P t h (try e' catch(C' V) e2, xs) (try (Val v) catch(C' V) e2, loc)" by(rule Try_\<tau>red1r_xt)
    hence "\<tau>red1r P t h (try e' catch(C' V) e2, xs) (Val v, loc)"
      by(auto intro: rtranclp.rtrancl_into_rtrancl Red1Try \<tau>move1TryRed)
    moreover have \<tau>: "\<tau>move2 (compP2 P) h [v] (try e catch(C' V) e2) pc None" by(simp add: \<tau>move2_iff)
    moreover
    have "P,try e catch(C' V) e2,h \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (try e catch(C' V) e2)), None)"
      by(rule bisim1Val2) simp
    moreover have "nat (int (length (compE2 e)) + (int (length (compE2 e2)) + 2)) = length (compE2 (try e catch(C' V) e2))" by simp
    ultimately show ?thesis using exec stk xcp
      by(fastforce elim!: exec_meth.cases simp add: exec_move_def)
  qed
next
  case (bisim1TryCatch1 e n a xs stk loc pc C'' C' e2 V)
  note exec = \<open>?exec (try e catch(C' V) e2) [Addr a] loc (Suc (length (compE2 e))) None stk' loc' pc' xcp'\<close>
  note bisim2 = \<open>P,e2,h \<turnstile> (e2, loc[V := Addr a]) \<leftrightarrow> ([], loc[V := Addr a], 0, None)\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  hence [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
  from bisim2
  have "P, try e catch(C' V) e2, h \<turnstile> ({V:Class C'=None; e2}, loc[V := Addr a]) \<leftrightarrow> ([], loc[V := Addr a], Suc (Suc (length (compE2 e) + 0)), None)"
    by(rule bisim1TryCatch2)
  moreover have "\<tau>move2 (compP2 P) h [Addr a] (try e catch(C' V) e2) (Suc (length (compE2 e))) None" by(simp add: \<tau>move2_iff)
  ultimately show ?case using exec by(fastforce elim!: exec_meth.cases simp add: exec_move_def)
next
  case (bisim1TryCatch2 e2 n e' xs stk loc pc xcp e C' V)
  note IH = bisim1TryCatch2.IH(2)
  note bisim2 = \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim = \<open>\<And>xs. P,e,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note exec = \<open>?exec (try e catch(C' V) e2) stk loc (Suc (Suc (length (compE2 e) + pc))) xcp stk' loc' pc' xcp'\<close>
  note bsok = \<open>bsok (try e catch(C' V) e2) n\<close>
  with \<open>n + max_vars {V:Class C'=None; e'} \<le> length xs\<close>
  have len: "Suc n + max_vars e' \<le> length xs" and V: "V < length xs" by simp_all
  let ?pre = "compE2 e @ [Goto (int (length (compE2 e2)) + 2), Store V]"
  from exec have "exec_meth_d (compP2 P) (?pre @ compE2 e2)
    (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e2 0 0) @ [(0, length (compE2 e), \<lfloor>C'\<rfloor>, Suc (length (compE2 e)), 0)]) t
    h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 exec_move_def)
  hence exec': "exec_meth_d (compP2 P) (?pre @ compE2 e2) (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e2 0 0)) t
     h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(auto elim!: exec_meth.cases intro: exec_meth.intros simp add: match_ex_table_append matches_ex_entry_def)
  hence "?exec e2 stk loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
    unfolding exec_move_def by(rule exec_meth_drop_xt) auto
  from IH[OF this len _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] bsok obtain e'' xs''
    where bisim': "P,e2,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
    and red: "?red e' xs e'' xs'' e2 stk pc (pc' - length ?pre) xcp xcp'" by auto
  from red have "length xs'' = length xs"
    by(auto dest!: \<tau>red1r_preserves_len \<tau>red1t_preserves_len red1_preserves_len split: if_split_asm)
  with red V have "?red {V:Class C'=None; e'} xs {V:Class C'=None; e''} xs'' e2 stk pc (pc' - length ?pre) xcp xcp'"
    by(fastforce elim!: Block_None_\<tau>red1r_xt Block_None_\<tau>red1t_xt intro: Block1Red split: if_split_asm)
  moreover
  from bisim'
  have "P,try e catch(C' V) e2,h' \<turnstile> ({V:Class C'=None;e''}, xs'') \<leftrightarrow> (stk', loc', Suc (Suc (length (compE2 e) + (pc' - length ?pre))), xcp')"
    by(rule bisim1_bisims1.bisim1TryCatch2)
  moreover have "\<tau>move2 (compP2 P) h stk (try e catch(C' V) e2) (Suc (Suc (length (compE2 e) + pc))) xcp = \<tau>move2 (compP2 P) h stk e2 pc xcp"
    by(simp add: \<tau>move2_iff)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc) auto
  moreover hence "Suc (Suc (pc' - Suc (Suc 0))) = pc'" by simp
  moreover have "no_call2 e2 pc \<Longrightarrow> no_call2 (try e catch(C' V) e2) (Suc (Suc (length (compE2 e) + pc)))"
    by(simp add: no_call2_def)
  ultimately show ?case using red V by(fastforce simp add: eval_nat_numeral split: if_split_asm)
next
  case (bisim1TryFail e n a xs stk loc pc C'' C' e2 V)
  note bisim = \<open>P,e,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with \<open>?exec (try e catch(C' V) e2) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close> pc \<open>typeof_addr h a = \<lfloor>Class_type C''\<rfloor>\<close> \<open>\<not> P \<turnstile> C'' \<preceq>\<^sup>* C'\<close>
  have False by(auto elim!: exec_meth.cases simp add: matches_ex_entry_def compP2_def match_ex_table_append_not_pcs exec_move_def cname_of_def)
  thus ?case ..
next
  case (bisim1TryCatchThrow e2 n a xs stk loc pc e C' V)
  note bisim = \<open>P,e2,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)\<close>
  from bisim have pc: "pc < length (compE2 e2)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e2 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with \<open>?exec (try e catch(C' V) e2) stk loc (Suc (Suc (length (compE2 e) + pc))) \<lfloor>a\<rfloor> stk' loc' pc' xcp'\<close> pc
  have False apply(auto elim!: exec_meth.cases simp add: compxE2_size_convs match_ex_table_append_not_pcs exec_move_def)
    apply(auto dest!: match_ex_table_shift_pcD simp add: match_ex_table_append matches_ex_entry_def compP2_def)
    done
  thus ?case ..
next
  case bisims1Nil
  hence False by(auto elim!: exec_meth.cases simp add: exec_moves_def)
  thus ?case ..
next
  case (bisims1List1 e n e' xs stk loc pc xcp es)
  note IH1 = bisims1List1.IH(2)
  note IH2 = bisims1List1.IH(4)
  note exec = \<open>?execs (e # es) stk loc pc xcp stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)\<close>
  note bisim2 = \<open>P,es,h \<turnstile> (es, loc) [\<leftrightarrow>] ([], loc, 0, None)\<close>
  note len = \<open>n + max_varss (e' # es) \<le> length xs\<close>
  note bsok = \<open>bsoks (e # es) n\<close>
  from bisim1 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  from bisim1 have lenxs: "length xs = length loc" by(rule bisim1_length_xs)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'"
      by(auto simp add: compxEs2_size_convs exec_moves_def exec_move_def intro: exec_meth_take_xt)
    from True have "\<tau>moves2 (compP2 P) h stk (e # es) pc xcp = \<tau>move2 (compP2 P) h stk e pc xcp"
      by(simp add: \<tau>move2_iff \<tau>moves2_iff)
    moreover from True have "no_calls2 (e # es) pc = no_call2 e pc"
      by(simp add: no_call2_def no_calls2_def)
    ultimately show ?thesis
      using IH1[OF exec' _ _ \<open>P,h \<turnstile> stk [:\<le>] ST\<close> \<open>conf_xcp' (compP2 P) h xcp\<close>] bsok len 
      by(fastforce intro: bisim1_bisims1.bisims1List1 elim!: \<tau>red1r_inj_\<tau>reds1r \<tau>red1t_inj_\<tau>reds1t List1Red1)
  next
    case False
    with pc have pc [simp]: "pc = length (compE2 e)" by simp
    with bisim1 obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      and v: "is_val e' \<Longrightarrow> e' = Val v \<and> xs = loc" and call: "call1 e' = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len bsok have red: "\<tau>red1r P t h (e', xs) (Val v, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    hence "\<tau>reds1r P t h (e' # es, xs) (Val v # es, loc)" by(rule \<tau>red1r_inj_\<tau>reds1r)
    moreover from exec stk xcp
    have exec': "exec_meth_d (compP2 P) (compE2 e @ compEs2 es) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxEs2 es 0 0))) t h ([] @ [v], loc, length (compE2 e) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxEs2 stack_xlift_compxEs2 exec_moves_def)
    hence "exec_meth_d (compP2 P) (compEs2 es) (stack_xlift (length [v]) (compxEs2 es 0 0)) t h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_drop_xt) auto
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_moves_d P t es h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 e), xcp')"
      by(unfold exec_moves_def)(drule (1) exec_meth_stk_splits, auto)
    from IH2[OF exec''] len lenxs bsok obtain es'' xs''
      where bisim': "P,es,h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk'', loc', pc' - length (compE2 e), xcp')"
      and red': "?reds es loc es'' xs'' es [] 0 (pc' - length (compE2 e)) None xcp'" by fastforce
    from bisim' have "P,e # es,h' \<turnstile> (Val v # es'', xs'') [\<leftrightarrow>] (stk'' @ [v], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
      by(rule bisims1List2)
    moreover from exec''
    have "\<tau>moves2 (compP2 P) h [v] (e # es) (length (compE2 e)) None = \<tau>moves2 (compP2 P) h [] es 0 None"
      using \<tau>instr_stk_drop_exec_moves[where stk="[]" and vs="[v]"] by(simp add: \<tau>moves2_iff)
    moreover have \<tau>: "\<And>es'. \<tau>moves1 P h (Val v # es') \<Longrightarrow> \<tau>moves1 P h es'" by simp
    from exec' have "pc' \<ge> length (compE2 e)"
      by(rule exec_meth_drop_xt_pc) auto
    moreover have "no_calls2 es 0 \<Longrightarrow> no_calls2 (e # es) (length (compE2 e))"
      by(simp add: no_calls2_def)
    ultimately show ?thesis using red' xcp stk stk' call v
      apply(auto simp add: split_paired_Ex)
      apply(blast 25 intro: rtranclp_trans rtranclp_tranclp_tranclp \<tau>reds1r_cons_\<tau>reds1r List1Red2 \<tau>reds1t_cons_\<tau>reds1t dest: \<tau>)+
      done
  qed
next
  case (bisims1List2 es n es' xs stk loc pc xcp e v)
  note IH = bisims1List2.IH(2)
  note exec = \<open>?execs (e # es) (stk @ [v]) loc (length (compE2 e) + pc) xcp stk' loc' pc' xcp'\<close>
  note bisim1 = \<open>P,e,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)\<close>
  note bisim2 = \<open>P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)\<close>
  note len = \<open>n + max_varss (Val v # es') \<le> length xs\<close>
  note bsok = \<open>bsoks (e # es) n\<close>
  from \<open>P,h \<turnstile> stk @ [v] [:\<le>] ST\<close> obtain ST' where ST': "P,h \<turnstile> stk [:\<le>] ST'"
    by(auto simp add: list_all2_append1)
  from exec have exec': "exec_meth_d (compP2 P) (compE2 e @ compEs2 es) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxEs2 es 0 0))) t h (stk @ [v], loc, length (compE2 e) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxEs2 stack_xlift_compxEs2 exec_moves_def)
  hence "exec_meth_d (compP2 P) (compEs2 es) (stack_xlift (length [v]) (compxEs2 es 0 0)) t h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
    by(rule exec_meth_drop_xt) auto
  with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
    and exec'': "exec_moves_d P t es h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e), xcp')"
    by(unfold exec_moves_def)(drule (1) exec_meth_stk_splits, auto)
  from IH[OF exec'' _ _ ST' \<open>conf_xcp' (compP2 P) h xcp\<close>] len bsok obtain es'' xs''
    where bisim': "P,es,h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk'', loc', pc' - length (compE2 e), xcp')"
    and red': "?reds es' xs es'' xs'' es stk pc (pc' - length (compE2 e)) xcp xcp'" by auto
  from bisim' have "P,e # es,h' \<turnstile> (Val v # es'', xs'') [\<leftrightarrow>] (stk'' @ [v], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
    by(rule bisim1_bisims1.bisims1List2)
  moreover from exec'' have "\<tau>moves2 (compP2 P) h (stk @ [v]) (e # es) (length (compE2 e) + pc) xcp = \<tau>moves2 (compP2 P) h stk es pc xcp"
    by(auto simp add: \<tau>moves2_iff \<tau>instr_stk_drop_exec_moves)
  moreover have \<tau>: "\<And>es'. \<tau>moves1 P h (Val v # es') \<Longrightarrow> \<tau>moves1 P h es'" by simp
  from exec' have "pc' \<ge> length (compE2 e)"
    by(rule exec_meth_drop_xt_pc) auto
  moreover have "no_calls2 es pc \<Longrightarrow> no_calls2 (e # es) (length (compE2 e) + pc)"
    by(simp add: no_calls2_def)
  ultimately show ?case using red' stk'
    by(auto split: if_split_asm simp add: split_paired_Ex)(blast intro: rtranclp_trans rtranclp_tranclp_tranclp \<tau>reds1r_cons_\<tau>reds1r List1Red2 \<tau>reds1t_cons_\<tau>reds1t dest: \<tau>)+
qed

end

inductive sim21_size_aux :: "nat \<Rightarrow> (pc \<times> 'addr option) \<Rightarrow> (pc \<times> 'addr option) \<Rightarrow> bool"
for len :: nat
where
  "\<lbrakk> pc1 \<le> len; pc2 \<le> len; xcp1 \<noteq> None \<and> xcp2 = None \<and> pc1 = pc2 \<or> xcp1 = None \<and> pc1 > pc2 \<rbrakk>
  \<Longrightarrow> sim21_size_aux len (pc1, xcp1) (pc2, xcp2)"

definition sim21_size :: "'addr jvm_prog \<Rightarrow> 'addr jvm_thread_state \<Rightarrow> 'addr jvm_thread_state \<Rightarrow> bool"
where
  "sim21_size P xcpfrs xcpfrs' \<longleftrightarrow>
   (xcpfrs, xcpfrs') \<in> 
   inv_image (less_than <*lex*> same_fst (\<lambda>n. True) (\<lambda>n. {(pcxcp, pcxcp'). sim21_size_aux n pcxcp pcxcp'}))
             (\<lambda>(xcp, frs). (length frs, case frs of [] \<Rightarrow> undefined
                          | (stk, loc, C, M, pc) # frs \<Rightarrow> (length (fst (snd (snd (the (snd (snd (snd (method P C M)))))))), pc, xcp)))"

lemma wfP_sim21_size_aux: "wfP (sim21_size_aux n)"
proof -
  let ?f = "\<lambda>(pc, xcp). case xcp of None \<Rightarrow> Suc (2 * (n - pc)) | Some _ \<Rightarrow> 2 * (n - pc)"
  have "wf {(m, m'). (m :: nat) < m'}" by(rule wf_less)
  hence "wf (inv_image {(m, m'). m < m'} ?f)" by(rule wf_inv_image)
  moreover have "{(pcxcp1, pcxcp2). sim21_size_aux n pcxcp1 pcxcp2} \<subseteq> inv_image {(m, m'). m < m'} ?f"
    by(auto elim!: sim21_size_aux.cases)
  ultimately show ?thesis unfolding wfP_def by(rule wf_subset)
qed

lemma Collect_split_mem: "{(x, y). (x, y) \<in> Q} = Q" by simp

lemma wfP_sim21_size: "wfP (sim21_size P)"
unfolding wfP_def Collect_split_mem sim21_size_def [abs_def]
apply(rule wf_inv_image)
apply(rule wf_lex_prod)
 apply(rule wf_less_than)
apply(rule wf_same_fst)
apply(rule wfP_sim21_size_aux[unfolded wfP_def])
done

declare split_beta[simp]

context J1_JVM_heap_base begin

lemma bisim1_Invoke_\<tau>Red:
  "\<lbrakk> P,E,h \<turnstile> (e, xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None); pc < length (compE2 E);
     compE2 E ! pc = Invoke M (length vs); n + max_vars e \<le> length xs; bsok E n \<rbrakk>
  \<Longrightarrow> \<exists>e' xs'. \<tau>red1r P t h (e, xs) (e', xs') \<and> P,E,h \<turnstile> (e', xs') \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None) \<and> call1 e' = \<lfloor>(a, M, vs)\<rfloor>"
  (is "\<lbrakk> _; _; _; _; _ \<rbrakk> \<Longrightarrow> ?concl e xs E n pc stk' loc")

  and bisims1_Invoke_\<tau>Reds:
  "\<lbrakk> P,Es,h \<turnstile> (es, xs) [\<leftrightarrow>] (rev vs @ Addr a # stk', loc, pc, None); pc < length (compEs2 Es);
    compEs2 Es ! pc = Invoke M (length vs); n + max_varss es \<le> length xs; bsoks Es n \<rbrakk>
  \<Longrightarrow> \<exists>es' xs'. \<tau>reds1r P t h (es, xs) (es', xs') \<and> P,Es,h \<turnstile> (es', xs') [\<leftrightarrow>] (rev vs @ Addr a # stk', loc, pc, None) \<and> calls1 es' = \<lfloor>(a, M, vs)\<rfloor>"
  (is "\<lbrakk> _; _; _; _; _ \<rbrakk> \<Longrightarrow> ?concls es xs Es n pc stk' loc")
proof(induct E n e xs stk\<equiv>"rev vs @ Addr a # stk'" loc pc xcp\<equiv>"None::'addr option"
  and Es n es xs stk\<equiv>"rev vs @ Addr a # stk'" loc pc xcp\<equiv>"None::'addr option"
  arbitrary: stk' and stk' rule: bisim1_bisims1_inducts_split)
  case bisim1Val2 thus ?case by simp
next
  case bisim1New thus ?case by simp
next
  case bisim1NewArray thus ?case
    by(fastforce split: if_split_asm intro: bisim1_bisims1.bisim1NewArray dest: bisim1_pc_length_compE2 elim!: NewArray_\<tau>red1r_xt)
next
  case bisim1Cast thus ?case
    by(fastforce split: if_split_asm intro: bisim1_bisims1.bisim1Cast dest: bisim1_pc_length_compE2 elim!: Cast_\<tau>red1r_xt)
next
  case bisim1InstanceOf thus ?case
    by(fastforce split: if_split_asm intro: bisim1_bisims1.bisim1InstanceOf dest: bisim1_pc_length_compE2 elim!: InstanceOf_\<tau>red1r_xt)
next
  case bisim1Val thus ?case by simp
next
  case bisim1Var thus ?case by simp
next
  case bisim1BinOp1 thus ?case
    apply(auto split: if_split_asm intro: bisim1_bisims1.bisim1BinOp1 dest: bisim1_pc_length_compE2 elim: BinOp_\<tau>red1r_xt1)
    apply(fastforce elim!: BinOp_\<tau>red1r_xt1 intro: bisim1_bisims1.bisim1BinOp1)
    done
next
  case (bisim1BinOp2 e2 n e' xs stk loc pc e1 bop v1)
  note IH = \<open>\<And>stk'. \<lbrakk>stk = rev vs @ Addr a # stk'; pc < length (compE2 e2); compE2 e2 ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs; bsok e2 n
                      \<rbrakk> \<Longrightarrow> ?concl e' xs e2 n pc stk' loc\<close>
  note inv = \<open>compE2 (e1 \<guillemotleft>bop\<guillemotright> e2) ! (length (compE2 e1) + pc) = Invoke M (length vs)\<close>
  with \<open>length (compE2 e1) + pc < length (compE2 (e1 \<guillemotleft>bop\<guillemotright> e2))\<close> have pc: "pc < length (compE2 e2)"
    by(auto split: bop.splits if_split_asm)
  moreover with inv have "compE2 e2 ! pc = Invoke M (length vs)" by simp
  moreover with \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close> pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisim1_Invoke_stkD)
  with \<open>stk @ [v1] = rev vs @ Addr a # stk'\<close> obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v1]"
    by(cases stk' rule: rev_cases) auto
  from \<open>n + max_vars (Val v1 \<guillemotleft>bop\<guillemotright> e') \<le> length xs\<close> have "n + max_vars e' \<le> length xs" by simp
  moreover from \<open>bsok (e1 \<guillemotleft>bop\<guillemotright> e2) n\<close> have "bsok e2 n" by simp
  ultimately have "?concl e' xs e2 n pc stk''' loc" using stk''' by-(rule IH)
  then obtain e'' xs' where IH': "\<tau>red1r P t h (e', xs) (e'', xs')" "call1 e'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,e2,h \<turnstile> (e'', xs') \<leftrightarrow> (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim have "P,e1\<guillemotleft>bop\<guillemotright>e2,h \<turnstile> (Val v1 \<guillemotleft>bop\<guillemotright> e'', xs') \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v1], loc, length (compE2 e1) + pc, None)"
    by(rule bisim1_bisims1.bisim1BinOp2)
  with IH' stk show ?case by(fastforce elim!: BinOp_\<tau>red1r_xt2)
next
  case bisim1LAss1 thus ?case
    by(fastforce split: if_split_asm intro: bisim1_bisims1.bisim1LAss1 dest: bisim1_pc_length_compE2 elim!: LAss_\<tau>red1r)
next
  case bisim1LAss2 thus ?case by simp
next
  case bisim1AAcc1 thus ?case
    apply(auto split: if_split_asm intro: bisim1_bisims1.bisim1AAcc1 dest: bisim1_pc_length_compE2 elim!: AAcc_\<tau>red1r_xt1)
    apply(fastforce elim!: AAcc_\<tau>red1r_xt1 intro: bisim1_bisims1.bisim1AAcc1)
    done
next
  case (bisim1AAcc2 e2 n e' xs stk loc pc e1 v1)
  note IH = \<open>\<And>stk'. \<lbrakk>stk = rev vs @ Addr a # stk'; pc < length (compE2 e2); compE2 e2 ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs; bsok e2 n
                      \<rbrakk> \<Longrightarrow> ?concl e' xs e2 n pc stk' loc\<close>
  note inv = \<open>compE2 (e1\<lfloor>e2\<rceil>) ! (length (compE2 e1) + pc) = Invoke M (length vs)\<close>
  with \<open>length (compE2 e1) + pc < length (compE2 (e1\<lfloor>e2\<rceil>))\<close> have pc: "pc < length (compE2 e2)"
    by(auto split: if_split_asm)
  moreover with inv have "compE2 e2 ! pc = Invoke M (length vs)" by simp
  moreover with \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close> pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisim1_Invoke_stkD)
  with \<open>stk @ [v1] = rev vs @ Addr a # stk'\<close> obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v1]"
    by(cases stk' rule: rev_cases) auto
  from \<open>n + max_vars (Val v1\<lfloor>e'\<rceil>) \<le> length xs\<close> have "n + max_vars e' \<le> length xs" by simp
  moreover from \<open>bsok (e1\<lfloor>e2\<rceil>) n\<close> have "bsok e2 n" by simp
  ultimately have "?concl e' xs e2 n pc stk''' loc" using stk''' by-(rule IH)
  then obtain e'' xs' where IH': "\<tau>red1r P t h (e', xs) (e'', xs')" "call1 e'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,e2,h \<turnstile> (e'', xs') \<leftrightarrow> (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim have "P,e1\<lfloor>e2\<rceil>,h \<turnstile> (Val v1\<lfloor>e''\<rceil>, xs') \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v1], loc, length (compE2 e1) + pc, None)"
    by(rule bisim1_bisims1.bisim1AAcc2)
  with IH' stk show ?case by(fastforce elim!: AAcc_\<tau>red1r_xt2)
next
  case (bisim1AAss1 e n e' xs loc pc e2 e3)
  note IH = \<open>\<lbrakk> pc < length (compE2 e); compE2 e ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs; bsok e n
             \<rbrakk> \<Longrightarrow> ?concl e' xs e n pc stk' loc\<close>
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None)\<close>
  note len = \<open>n + max_vars (e'\<lfloor>e2\<rceil> := e3) \<le> length xs\<close>
  hence len': "n + max_vars e' \<le> length xs" by simp
  note inv = \<open>compE2 (e\<lfloor>e2\<rceil> := e3) ! pc = Invoke M (length vs)\<close>
  with \<open>pc < length (compE2 (e\<lfloor>e2\<rceil> := e3))\<close> bisim have pc: "pc < length (compE2 e)"
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2)
  moreover with inv have "compE2 e ! pc = Invoke M (length vs)" by simp
  moreover from \<open>bsok (e\<lfloor>e2\<rceil> := e3) n\<close> have "bsok e n" by simp
  ultimately have "?concl e' xs e n pc stk' loc" using len' by-(rule IH)
  thus ?case
    by(fastforce intro: bisim1_bisims1.bisim1AAss1 elim!: AAss_\<tau>red1r_xt1)
next
  case (bisim1AAss2 e2 n e' xs stk loc pc e1 e3 v1)
  note IH = \<open>\<And>stk'. \<lbrakk>stk = rev vs @ Addr a # stk'; pc < length (compE2 e2); compE2 e2 ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs; bsok e2 n
                      \<rbrakk> \<Longrightarrow> ?concl e' xs e2 n pc stk' loc\<close>
  note inv = \<open>compE2 (e1\<lfloor>e2\<rceil> := e3) ! (length (compE2 e1) + pc) = Invoke M (length vs)\<close>
  note bisim = \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  with inv \<open>length (compE2 e1) + pc < length (compE2 (e1\<lfloor>e2\<rceil> := e3))\<close> have pc: "pc < length (compE2 e2)"
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2)
  moreover with inv have "compE2 e2 ! pc = Invoke M (length vs)" by simp
  moreover with bisim pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisim1_Invoke_stkD)
  with \<open>stk @ [v1] = rev vs @ Addr a # stk'\<close> obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v1]"
    by(cases stk' rule: rev_cases) auto
  from \<open>n + max_vars (Val v1\<lfloor>e'\<rceil> := e3) \<le> length xs\<close> have "n + max_vars e' \<le> length xs" by simp
  moreover from \<open>bsok (e1\<lfloor>e2\<rceil> := e3) n\<close> have "bsok e2 n" by simp
  ultimately have "?concl e' xs e2 n pc stk''' loc" using stk''' by-(rule IH)
  then obtain e'' xs' where IH': "\<tau>red1r P t h (e', xs) (e'', xs')" "call1 e'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,e2,h \<turnstile> (e'', xs') \<leftrightarrow> (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim
  have "P,e1\<lfloor>e2\<rceil> := e3,h \<turnstile> (Val v1\<lfloor>e''\<rceil> := e3, xs') \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v1], loc, length (compE2 e1) + pc, None)"
    by(rule bisim1_bisims1.bisim1AAss2)
  with IH' stk show ?case by(fastforce elim!: AAss_\<tau>red1r_xt2)
next
  case (bisim1AAss3 e3 n e' xs stk loc pc e1 e2 v1 v2)
  note IH = \<open>\<And>stk'. \<lbrakk>stk = rev vs @ Addr a # stk'; pc < length (compE2 e3); compE2 e3 ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs; bsok e3 n
                      \<rbrakk> \<Longrightarrow> ?concl e' xs e3 n pc stk' loc\<close>
  note inv = \<open>compE2 (e1\<lfloor>e2\<rceil> := e3) ! (length (compE2 e1) + length (compE2 e2) + pc) = Invoke M (length vs)\<close>
  with \<open>length (compE2 e1) + length (compE2 e2) + pc < length (compE2 (e1\<lfloor>e2\<rceil> := e3))\<close>
  have pc: "pc < length (compE2 e3)" by(simp add: nth_Cons split: nat.split_asm if_split_asm)
  moreover with inv have "compE2 e3 ! pc = Invoke M (length vs)" by simp
  moreover with \<open>P,e3,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>  pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisim1_Invoke_stkD)
  with \<open>stk @ [v2, v1] = rev vs @ Addr a # stk'\<close> obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v2, v1]"
    by(cases stk' rule: rev_cases) auto
  from \<open>n + max_vars (Val v1\<lfloor>Val v2\<rceil> := e') \<le> length xs\<close> have "n + max_vars e' \<le> length xs" by simp
  moreover from \<open>bsok (e1\<lfloor>e2\<rceil> := e3) n\<close> have "bsok e3 n" by simp
  ultimately have "?concl e' xs e3 n pc stk''' loc" using stk''' by-(rule IH)
  then obtain e'' xs' where IH': "\<tau>red1r P t h (e', xs) (e'', xs')" "call1 e'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,e3,h \<turnstile> (e'', xs') \<leftrightarrow> (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim
  have "P,e1\<lfloor>e2\<rceil> := e3,h \<turnstile> (Val v1\<lfloor>Val v2\<rceil> := e'', xs') \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v2, v1], loc, length (compE2 e1) + length (compE2 e2) + pc, None)"
    by -(rule bisim1_bisims1.bisim1AAss3, auto)
  with IH' stk show ?case by(fastforce elim!: AAss_\<tau>red1r_xt3)
next
  case bisim1AAss4 thus ?case by simp
next
  case bisim1ALength thus ?case
    by(fastforce split: if_split_asm intro: bisim1_bisims1.bisim1ALength dest: bisim1_pc_length_compE2 elim!: ALength_\<tau>red1r_xt)
next
  case bisim1FAcc thus ?case
    by(fastforce split: if_split_asm intro: bisim1_bisims1.bisim1FAcc dest: bisim1_pc_length_compE2 elim!: FAcc_\<tau>red1r_xt)
next
  case bisim1FAss1 thus ?case
    apply(auto split: if_split_asm intro: bisim1_bisims1.bisim1FAss1 dest: bisim1_pc_length_compE2 elim!: FAss_\<tau>red1r_xt1)
    by(fastforce intro: bisim1_bisims1.bisim1FAss1 elim!: FAss_\<tau>red1r_xt1)
next
  case (bisim1FAss2 e2 n e' xs stk loc pc e1 F D v1)
  note IH = \<open>\<And>stk'. \<lbrakk>stk = rev vs @ Addr a # stk'; pc < length (compE2 e2); compE2 e2 ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs; bsok e2 n
                      \<rbrakk> \<Longrightarrow> ?concl e' xs e2 n pc stk' loc\<close>
  note inv = \<open>compE2 (e1\<bullet>F{D} := e2) ! (length (compE2 e1) + pc) = Invoke M (length vs)\<close>
  with \<open>length (compE2 e1) + pc < length (compE2 (e1\<bullet>F{D} := e2))\<close> have pc: "pc < length (compE2 e2)"
    by(simp split: if_split_asm nat.split_asm add: nth_Cons)
  moreover with inv have "compE2 e2 ! pc = Invoke M (length vs)" by simp
  moreover with \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close> pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisim1_Invoke_stkD)
  with \<open>stk @ [v1] = rev vs @ Addr a # stk'\<close> obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v1]"
    by(cases stk' rule: rev_cases) auto
  from \<open>n + max_vars (Val v1\<bullet>F{D} := e') \<le> length xs\<close> have "n + max_vars e' \<le> length xs" by simp
  moreover from \<open>bsok (e1\<bullet>F{D} := e2) n\<close> have "bsok e2 n" by simp
  ultimately have "?concl e' xs e2 n pc stk''' loc" using stk''' by-(rule IH)
  then obtain e'' xs' where IH': "\<tau>red1r P t h (e', xs) (e'', xs')" "call1 e'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,e2,h \<turnstile> (e'', xs') \<leftrightarrow> (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim have "P,e1\<bullet>F{D} := e2,h \<turnstile> (Val v1\<bullet>F{D} := e'', xs') \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v1], loc, length (compE2 e1) + pc, None)"
    by(rule bisim1_bisims1.bisim1FAss2)
  with IH' stk show ?case by(fastforce elim!: FAss_\<tau>red1r_xt2)
next
  case bisim1FAss3 thus ?case by simp
next
  case (bisim1CAS1 e n e' xs loc pc e2 e3 D F)
  note IH = \<open>\<lbrakk> pc < length (compE2 e); compE2 e ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs; bsok e n
             \<rbrakk> \<Longrightarrow> ?concl e' xs e n pc stk' loc\<close>
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None)\<close>
  note len = \<open>n + max_vars _ \<le> length xs\<close>
  hence len': "n + max_vars e' \<le> length xs" by simp
  note inv = \<open>compE2 _ ! pc = Invoke M (length vs)\<close>
  with \<open>pc < length _\<close> bisim have pc: "pc < length (compE2 e)"
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2)
  moreover with inv have "compE2 e ! pc = Invoke M (length vs)" by simp
  moreover from \<open>bsok _ n\<close> have "bsok e n" by simp
  ultimately have "?concl e' xs e n pc stk' loc" using len' by-(rule IH)
  thus ?case
    by(fastforce intro: bisim1_bisims1.bisim1CAS1 elim!: CAS_\<tau>red1r_xt1)
next
  case (bisim1CAS2 e2 n e' xs stk loc pc e1 e3 D F v1)
  note IH = \<open>\<And>stk'. \<lbrakk>stk = rev vs @ Addr a # stk'; pc < length (compE2 e2); compE2 e2 ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs; bsok e2 n
                      \<rbrakk> \<Longrightarrow> ?concl e' xs e2 n pc stk' loc\<close>
  note inv = \<open>compE2 _ ! (length (compE2 e1) + pc) = Invoke M (length vs)\<close>
  note bisim = \<open>P,e2,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>
  with inv \<open>length (compE2 e1) + pc < length (compE2 _)\<close> have pc: "pc < length (compE2 e2)"
    by(auto split: if_split_asm dest: bisim1_pc_length_compE2)
  moreover with inv have "compE2 e2 ! pc = Invoke M (length vs)" by simp
  moreover with bisim pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisim1_Invoke_stkD)
  with \<open>stk @ [v1] = rev vs @ Addr a # stk'\<close> obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v1]"
    by(cases stk' rule: rev_cases) auto
  from \<open>n + max_vars _ \<le> length xs\<close> have "n + max_vars e' \<le> length xs" by simp
  moreover from \<open>bsok _ n\<close> have "bsok e2 n" by simp
  ultimately have "?concl e' xs e2 n pc stk''' loc" using stk''' by-(rule IH)
  then obtain e'' xs' where IH': "\<tau>red1r P t h (e', xs) (e'', xs')" "call1 e'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,e2,h \<turnstile> (e'', xs') \<leftrightarrow> (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim
  have "P,e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3),h \<turnstile> (Val v1\<bullet>compareAndSwap(D\<bullet>F, e'', e3), xs') \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v1], loc, length (compE2 e1) + pc, None)"
    by(rule bisim1_bisims1.bisim1CAS2)
  with IH' stk show ?case by(fastforce elim!: CAS_\<tau>red1r_xt2)
next
  case (bisim1CAS3 e3 n e' xs stk loc pc e1 e2 D F v1 v2)
  note IH = \<open>\<And>stk'. \<lbrakk>stk = rev vs @ Addr a # stk'; pc < length (compE2 e3); compE2 e3 ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs; bsok e3 n
                      \<rbrakk> \<Longrightarrow> ?concl e' xs e3 n pc stk' loc\<close>
  note inv = \<open>compE2 _ ! (length (compE2 e1) + length (compE2 e2) + pc) = Invoke M (length vs)\<close>
  with \<open>length (compE2 e1) + length (compE2 e2) + pc < length (compE2 _)\<close>
  have pc: "pc < length (compE2 e3)" by(simp add: nth_Cons split: nat.split_asm if_split_asm)
  moreover with inv have "compE2 e3 ! pc = Invoke M (length vs)" by simp
  moreover with \<open>P,e3,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, None)\<close>  pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisim1_Invoke_stkD)
  with \<open>stk @ [v2, v1] = rev vs @ Addr a # stk'\<close> obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v2, v1]"
    by(cases stk' rule: rev_cases) auto
  from \<open>n + max_vars _ \<le> length xs\<close> have "n + max_vars e' \<le> length xs" by simp
  moreover from \<open>bsok _ n\<close> have "bsok e3 n" by simp
  ultimately have "?concl e' xs e3 n pc stk''' loc" using stk''' by-(rule IH)
  then obtain e'' xs' where IH': "\<tau>red1r P t h (e', xs) (e'', xs')" "call1 e'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,e3,h \<turnstile> (e'', xs') \<leftrightarrow> (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim
  have "P,e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3), h \<turnstile> (Val v1\<bullet>compareAndSwap(D\<bullet>F, Val v2, e''), xs') \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v2, v1], loc, length (compE2 e1) + length (compE2 e2) + pc, None)"
    by -(rule bisim1_bisims1.bisim1CAS3, auto)
  with IH' stk show ?case by(fastforce elim!: CAS_\<tau>red1r_xt3)
next
  case (bisim1Call1 obj n obj' xs loc pc ps M')
  note IH = \<open>\<lbrakk>pc < length (compE2 obj); compE2 obj ! pc = Invoke M (length vs); n + max_vars obj' \<le> length xs; bsok obj n
                     \<rbrakk> \<Longrightarrow> ?concl obj' xs obj n pc stk' loc\<close>
  note bisim = \<open>P,obj,h \<turnstile> (obj', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None)\<close>
  note len = \<open>n + max_vars (obj'\<bullet>M'(ps)) \<le> length xs\<close>
  hence len': "n + max_vars obj' \<le> length xs" by simp
  from \<open>bsok (obj\<bullet>M'(ps)) n\<close> have bsok: "bsok obj n" by simp
  note inv = \<open>compE2 (obj\<bullet>M'(ps)) ! pc = Invoke M (length vs)\<close>
  with \<open>pc < length (compE2 (obj\<bullet>M'(ps)))\<close> bisim
  have pc: "pc < length (compE2 obj) \<or> ps = [] \<and> pc = length (compE2 obj)"
    by(cases ps)(auto split: if_split_asm dest: bisim1_pc_length_compE2)
  thus ?case
  proof
    assume "pc < length (compE2 obj)"
    moreover with inv have "compE2 obj ! pc = Invoke M (length vs)" by simp
    ultimately have "?concl obj' xs obj n pc stk' loc" using len' bsok by(rule IH)
    thus ?thesis by(fastforce intro: bisim1_bisims1.bisim1Call1 elim!: Call_\<tau>red1r_obj)
  next
    assume [simp]: "ps = [] \<and> pc = length (compE2 obj)"
    with inv have [simp]: "vs = []" "M' = M" by simp_all
    with bisim have [simp]: "vs = []" "stk' = []" by(auto dest: bisim1_pc_length_compE2D)
    with bisim len' bsok have "\<tau>red1r P t h (obj', xs) (addr a, loc)"
      by(auto intro: bisim1_Val_\<tau>red1r simp add: bsok_def)
    moreover
    have "P,obj\<bullet>M([]),h \<turnstile> (addr a\<bullet>M([]), loc) \<leftrightarrow> ([Addr a], loc, length (compE2 obj), None)"
      by(rule bisim1_bisims1.bisim1Call1[OF bisim1Val2]) simp_all
    ultimately show ?thesis by auto(fastforce elim!: Call_\<tau>red1r_obj)
  qed
next
  case (bisim1CallParams ps n ps' xs stk loc pc obj M' v)
  note IH = \<open>\<And>stk'. \<lbrakk>stk = rev vs @ Addr a # stk'; pc < length (compEs2 ps); compEs2 ps ! pc = Invoke M (length vs); n + max_varss ps' \<le> length xs; bsoks ps n
                     \<rbrakk> \<Longrightarrow> ?concls ps' xs ps n pc stk' loc\<close>
  note bisim = \<open>P,ps,h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, None)\<close>
  note len = \<open>n + max_vars (Val v\<bullet>M'(ps')) \<le> length xs\<close>
  hence len': "n + max_varss ps' \<le> length xs" by simp
  note stk = \<open>stk @ [v] = rev vs @ Addr a # stk'\<close>
  note inv = \<open>compE2 (obj\<bullet>M'(ps)) ! (length (compE2 obj) + pc) = Invoke M (length vs)\<close>
  from \<open>bsok (obj\<bullet>M'(ps)) n\<close> have bsok: "bsoks ps n" by simp
  from \<open>length (compE2 obj) + pc < length (compE2 (obj\<bullet>M'(ps)))\<close> 
  have "pc < length (compEs2 ps) \<or> pc = length (compEs2 ps)" by(auto)
  thus ?case
  proof
    assume pc: "pc < length (compEs2 ps)"
    moreover with inv have "compEs2 ps ! pc = Invoke M (length vs)" by simp
    moreover with bisim pc
    obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
      by(auto dest!: bisims1_Invoke_stkD)
    with \<open>stk @ [v] = rev vs @ Addr a # stk'\<close> obtain stk'''
      where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v]"
      by(cases stk' rule: rev_cases) auto
    note len' stk'''
    ultimately have "?concls ps' xs ps n pc stk''' loc" using bsok by-(rule IH)
    then obtain es'' xs' where IH': "\<tau>reds1r P t h (ps', xs) (es'', xs')" "calls1 es'' = \<lfloor>(a, M, vs)\<rfloor>"
      and bisim: "P,ps,h \<turnstile> (es'', xs') [\<leftrightarrow>] (rev vs @ Addr a # stk''', loc, pc, None)" by blast
    from bisim have "P,obj\<bullet>M'(ps),h \<turnstile> (Val v\<bullet>M'(es''), xs') \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v], loc, length (compE2 obj) + pc, None)"
      by(rule bisim1_bisims1.bisim1CallParams)
    with IH' stk show ?case
      by(fastforce elim!: Call_\<tau>red1r_param simp add: is_vals_conv)
  next
    assume [simp]: "pc = length (compEs2 ps)"
    from bisim obtain vs' where [simp]: "stk = rev vs'"
      and psvs': "length ps = length vs'" by(auto dest: bisims1_pc_length_compEs2D)
    from inv have [simp]: "M' = M" and vsps: "length vs = length ps" by simp_all
    with stk psvs' have [simp]: "v = Addr a" "stk' = []" "vs' = vs" by simp_all
    from bisim len' bsok have "\<tau>reds1r P t h (ps', xs) (map Val vs, loc)"
      by(auto intro: bisims1_Val_\<tau>Reds1r simp add: bsoks_def)
    moreover from bisims1_map_Val_append[OF bisims1Nil vsps[symmetric], simplified, of P h loc]
    have "P,obj\<bullet>M(ps),h \<turnstile> (addr a\<bullet>M(map Val vs), loc) \<leftrightarrow> (rev vs @ [Addr a], loc, length (compE2 obj) + length (compEs2 ps), None)"
      by(rule bisim1_bisims1.bisim1CallParams)
    ultimately show ?thesis by(fastforce elim!: Call_\<tau>red1r_param)
  qed
next
  case bisim1BlockSome1 thus ?case by simp
next
  case bisim1BlockSome2 thus ?case by simp
next
  case (bisim1BlockSome4 e n e' xs loc pc V T v)
  note IH = \<open>\<lbrakk>pc < length (compE2 e); compE2 e ! pc = Invoke M (length vs); Suc n + max_vars e' \<le> length xs; bsok e (Suc n)
             \<rbrakk> \<Longrightarrow> ?concl e' xs e (Suc V) pc stk' loc\<close>
  from \<open>Suc (Suc pc) < length (compE2 {V:T=\<lfloor>v\<rfloor>; e})\<close> have "pc < length (compE2 e)" by simp
  moreover from \<open>compE2 {V:T=\<lfloor>v\<rfloor>; e} ! Suc (Suc pc) = Invoke M (length vs)\<close>
  have "compE2 e ! pc = Invoke M (length vs)" by simp
  moreover note len = \<open>n + max_vars {V:T=None; e'} \<le> length xs\<close>
  hence "Suc n + max_vars e' \<le> length xs" by simp
  moreover from \<open>bsok {V:T=\<lfloor>v\<rfloor>; e} n\<close> have "bsok e (Suc n)" by simp
  ultimately have "?concl e' xs e (Suc V) pc stk' loc" by(rule IH)
  then obtain e'' xs' where red: "\<tau>red1r P t h (e', xs) (e'', xs')"
    and bisim': "P,e,h \<turnstile> (e'', xs') \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None)"
    and call: "call1 e'' = \<lfloor>(a, M, vs)\<rfloor>" by blast
  from red have "\<tau>red1r P t h ({V:T=None; e'}, xs) ({V:T=None; e''}, xs')" by(rule Block_None_\<tau>red1r_xt)
  with bisim' call show ?case by(fastforce intro: bisim1_bisims1.bisim1BlockSome4)
next
  case (bisim1BlockNone e n e' xs loc pc V T)
  note IH = \<open>\<lbrakk>pc < length (compE2 e); compE2 e ! pc = Invoke M (length vs); Suc n + max_vars e' \<le> length xs; bsok e (Suc n)
              \<rbrakk> \<Longrightarrow> ?concl e' xs e (Suc V) pc stk' loc\<close>
  from \<open>pc < length (compE2 {V:T=None; e})\<close> have "pc < length (compE2 e)" by simp
  moreover from \<open>compE2 {V:T=None; e} ! pc = Invoke M (length vs)\<close>
  have "compE2 e ! pc = Invoke M (length vs)" by simp
  moreover note len = \<open>n + max_vars {V:T=None; e'} \<le> length xs\<close>
  hence "Suc n + max_vars e' \<le> length xs" by simp
  moreover from \<open>bsok {V:T=None; e} n\<close> have "bsok e (Suc n)" by simp
  ultimately have "?concl e' xs e (Suc V) pc stk' loc" by(rule IH)
  then obtain e'' xs' where red: "\<tau>red1r P t h (e', xs) (e'', xs')"
    and bisim': "P,e,h \<turnstile> (e'', xs') \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None)"
    and call: "call1 e'' = \<lfloor>(a, M, vs)\<rfloor>" by blast
  from red have "\<tau>red1r P t h ({V:T=None; e'}, xs) ({V:T=None; e''}, xs')" by(rule Block_None_\<tau>red1r_xt)
  with bisim' call show ?case by(fastforce intro: bisim1_bisims1.bisim1BlockNone)
next
  case bisim1Sync1 thus ?case
    apply(auto split: if_split_asm intro: bisim1_bisims1.bisim1Sync1 dest: bisim1_pc_length_compE2 elim!: Sync_\<tau>red1r_xt)
    by(fastforce split: if_split_asm intro: bisim1_bisims1.bisim1Sync1 elim!: Sync_\<tau>red1r_xt)
next
  case bisim1Sync2 thus ?case by simp
next
  case bisim1Sync3 thus ?case by simp
next
  case bisim1Sync4 thus ?case
    apply(auto split: if_split_asm intro: bisim1_bisims1.bisim1Sync4 dest: bisim1_pc_length_compE2 elim!: InSync_\<tau>red1r_xt)
    by(fastforce split: if_split_asm intro: bisim1_bisims1.bisim1Sync4 elim!: InSync_\<tau>red1r_xt)
next
  case bisim1Sync5 thus ?case by simp
next
  case bisim1Sync6 thus ?case by simp
next
  case bisim1Sync7 thus ?case by simp
next
  case bisim1Sync8 thus ?case by simp
next
  case bisim1Sync9 thus ?case by simp
next
  case bisim1InSync thus ?case by simp
next
  case bisim1Seq1 thus ?case
    apply(auto split: if_split_asm intro: bisim1_bisims1.bisim1Seq1 dest: bisim1_pc_length_compE2 elim!: Seq_\<tau>red1r_xt)
    by(fastforce split: if_split_asm intro: bisim1_bisims1.bisim1Seq1 elim!: Seq_\<tau>red1r_xt)
next
  case bisim1Seq2 thus ?case
    by(auto split: if_split_asm intro: bisim1_bisims1.bisim1Seq2 dest: bisim1_pc_length_compE2)
next
  case bisim1Cond1 thus ?case
    apply(clarsimp split: if_split_asm)
     apply(fastforce intro!: exI intro: bisim1_bisims1.bisim1Cond1 elim!: Cond_\<tau>red1r_xt)
    by(fastforce dest: bisim1_pc_length_compE2)
next
  case bisim1CondThen thus ?case
    apply(clarsimp split: if_split_asm)
     apply(fastforce intro!: exI intro: bisim1_bisims1.bisim1CondThen)
    by(fastforce dest: bisim1_pc_length_compE2)
next
  case bisim1CondElse thus ?case
    by(clarsimp split: if_split_asm)(fastforce intro!: exI intro: bisim1_bisims1.bisim1CondElse)
next
  case bisim1While1 thus ?case by simp
next
  case bisim1While3 thus ?case
    apply(auto split: if_split_asm intro: bisim1_bisims1.bisim1While3 dest: bisim1_pc_length_compE2 elim!: Cond_\<tau>red1r_xt)
    by(fastforce split: if_split_asm intro: bisim1_bisims1.bisim1While3 elim!: Cond_\<tau>red1r_xt)
next
  case bisim1While4 thus ?case
    apply(auto split: if_split_asm intro: bisim1_bisims1.bisim1While4 dest: bisim1_pc_length_compE2 elim!: Seq_\<tau>red1r_xt)
    by(fastforce split: if_split_asm intro: bisim1_bisims1.bisim1While4 elim!: Seq_\<tau>red1r_xt)
next
  case bisim1While6 thus ?case by simp
next
  case bisim1While7 thus ?case by simp
next
  case bisim1Throw1 thus ?case
    by(fastforce split: if_split_asm intro: bisim1_bisims1.bisim1Throw1 dest: bisim1_pc_length_compE2 elim!: Throw_\<tau>red1r_xt)
next
  case bisim1Try thus ?case
    apply(auto split: if_split_asm intro: bisim1_bisims1.bisim1Try dest: bisim1_pc_length_compE2 elim!: Try_\<tau>red1r_xt)
    by(fastforce split: if_split_asm intro: bisim1_bisims1.bisim1Try elim!: Try_\<tau>red1r_xt)
next
  case bisim1TryCatch1 thus ?case by simp
next
  case (bisim1TryCatch2 e n e' xs loc pc e1 C V)
  note IH = \<open>\<lbrakk>pc < length (compE2 e); compE2 e ! pc = Invoke M (length vs); Suc n + max_vars e' \<le> length xs; bsok e (Suc n)
             \<rbrakk> \<Longrightarrow> ?concl e' xs e (Suc V) pc stk' loc\<close>
  from \<open>Suc (Suc (length (compE2 e1) + pc)) < length (compE2 (try e1 catch(C V) e))\<close>
  have "pc < length (compE2 e)" by simp
  moreover from \<open>compE2 (try e1 catch(C V) e) ! Suc (Suc (length (compE2 e1) + pc)) = Invoke M (length vs)\<close>
  have "compE2 e ! pc = Invoke M (length vs)" by simp
  moreover note len = \<open>n + max_vars {V:Class C=None; e'} \<le> length xs\<close>
  hence "Suc n + max_vars e' \<le> length xs" by simp
  moreover from \<open>bsok (try e1 catch(C V) e) n\<close> have "bsok e (Suc n)" by simp
  ultimately have "?concl e' xs e (Suc V) pc stk' loc" by(rule IH)
  then obtain e'' xs' where red: "\<tau>red1r P t h (e', xs) (e'', xs')"
    and bisim': "P,e,h \<turnstile> (e'', xs') \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None)"
    and call: "call1 e'' = \<lfloor>(a, M, vs)\<rfloor>" by blast
  from red have "\<tau>red1r P t h ({V:Class C=None; e'}, xs) ({V:Class C=None; e''}, xs')" 
    by(rule Block_None_\<tau>red1r_xt)
  with bisim' call show ?case by(fastforce intro: bisim1_bisims1.bisim1TryCatch2)
next
  case bisims1Nil thus ?case by simp
next
  case (bisims1List1 e n e' xs loc pc es)
  note IH = \<open>\<lbrakk>pc < length (compE2 e); compE2 e ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs; bsok e n
             \<rbrakk> \<Longrightarrow> ?concl e' xs e n pc stk' loc\<close>
  note bisim = \<open>P,e,h \<turnstile> (e', xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None)\<close>
  note len = \<open>n + max_varss (e' # es) \<le> length xs\<close>
  hence len': "n + max_vars e' \<le> length xs" by simp
  from \<open>bsoks (e # es) n\<close> have bsok: "bsok e n" by simp
  note inv = \<open>compEs2 (e # es) ! pc = Invoke M (length vs)\<close>
  with \<open>pc < length (compEs2 (e # es))\<close> bisim have pc: "pc < length (compE2 e)"
    by(cases es)(auto split: if_split_asm dest: bisim1_pc_length_compE2)
  moreover with inv have "compE2 e ! pc = Invoke M (length vs)" by simp
  ultimately have "?concl e' xs e n pc stk' loc" using len' bsok by(rule IH)
  thus ?case by(fastforce intro: bisim1_bisims1.bisims1List1 elim!: \<tau>red1r_inj_\<tau>reds1r)
next
  case (bisims1List2 es n es' xs stk loc pc e v)
  note IH = \<open>\<And>stk'. \<lbrakk>stk = rev vs @ Addr a # stk'; pc < length (compEs2 es); compEs2 es ! pc = Invoke M (length vs); n + max_varss es' \<le> length xs; bsoks es n
                     \<rbrakk> \<Longrightarrow> ?concls es' xs es n pc stk' loc\<close>
  note bisim = \<open>P,es,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, None)\<close>
  note len = \<open>n + max_varss (Val v # es') \<le> length xs\<close>
  hence len': "n + max_varss es' \<le> length xs" by simp
  from \<open>bsoks (e # es) n\<close> have bsok: "bsoks es n" by simp
  note stk = \<open>stk @ [v] = rev vs @ Addr a # stk'\<close>
  note inv = \<open>compEs2 (e # es) ! (length (compE2 e) + pc) = Invoke M (length vs)\<close>
  from \<open>length (compE2 e) + pc < length (compEs2 (e # es))\<close> have pc: "pc < length (compEs2 es)" by auto
  moreover with inv have "compEs2 es ! pc = Invoke M (length vs)" by simp
  moreover with bisim pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisims1_Invoke_stkD)
  with \<open>stk @ [v] = rev vs @ Addr a # stk'\<close> obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v]"
    by(cases stk' rule: rev_cases) auto
  note len' stk'''
  ultimately have "?concls es' xs es n pc stk''' loc" using bsok by-(rule IH)
  then obtain es'' xs' where red: "\<tau>reds1r P t h (es', xs) (es'', xs')"
    and call: "calls1 es'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,es,h \<turnstile> (es'', xs') [\<leftrightarrow>] (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim have "P,e#es,h \<turnstile> (Val v # es'', xs') [\<leftrightarrow>]
                                          ((rev vs @ Addr a # stk''') @ [v], loc, length (compE2 e) + pc, None)" 
    by(rule bisim1_bisims1.bisims1List2)
  moreover from red have "\<tau>reds1r P t h (Val v # es', xs) (Val v # es'', xs')" by(rule \<tau>reds1r_cons_\<tau>reds1r)
  ultimately show ?case using stk call by fastforce
qed

end

declare split_beta [simp del]

context J1_JVM_conf_read begin

lemma \<tau>Red1_simulates_exec_1_\<tau>:
  assumes wf: "wf_J1_prog P"
  and exec: "exec_1_d (compP2 P) t (Normal (xcp, h, frs)) ta (Normal (xcp', h', frs'))"
  and bisim: "bisim1_list1 t h (e, xs) exs xcp frs"
  and \<tau>: "\<tau>Move2 (compP2 P) (xcp, h, frs)"
  shows "h = h' \<and> (\<exists>e' xs' exs'. (if sim21_size (compP2 P) (xcp', frs') (xcp, frs) then \<tau>Red1r else \<tau>Red1t) P t h ((e, xs), exs) ((e', xs'), exs') \<and> bisim1_list1 t h (e', xs') exs' xcp' frs')"
using bisim
proof(cases)
  case (bl1_Normal stk loc C M pc FRS Ts T body D)
  hence [simp]: "frs = (stk, loc, C, M, pc) # FRS"
    and conf: "compTP P \<turnstile> t: (xcp, h, (stk, loc, C, M, pc) # FRS) \<surd>"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>body\<rfloor> in D"
    and bisim: "P,blocks1 0 (Class D#Ts) body,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
    and lenxs: "max_vars e \<le> length xs"
    and bisims: "list_all2 (bisim1_fr P h) exs FRS" by auto
  from sees_method_compP[OF sees, where f="\<lambda>C M Ts T. compMb2"]
  have sees': "compP2 P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>(max_stack body, max_vars body, compE2 body @ [Return], compxE2 body 0 0)\<rfloor> in D"
    by(simp add: compP2_def compMb2_def)
  from bisim have pc: "pc \<le> length (compE2 body)" by(auto dest: bisim1_pc_length_compE2)
  from conf have hconf: "hconf h" "preallocated h" by(simp_all add: correct_state_def)

  from sees wf have bsok: "bsok (blocks1 0 (Class D # Ts) body) 0"
    by(auto dest!: sees_wf_mdecl simp add: bsok_def wf_mdecl_def WT1_expr_locks)

  from exec obtain check: "check (compP2 P) (xcp, h, frs)"
    and exec: "compP2 P,t \<turnstile> (xcp, h, frs) -ta-jvm\<rightarrow> (xcp', h', frs')"
    by(rule jvmd_NormalE)(auto simp add: exec_1_iff)

  from wt_compTP_compP2[OF wf] exec conf
  have conf': "compTP P \<turnstile> t:(xcp', h', frs') \<surd>" by(auto intro: BV_correct_1)

  from conf have tconf: "P,h \<turnstile> t \<surd>t" unfolding correct_state_def
    by(simp add: compP2_def tconf_def)

  show ?thesis
  proof(cases xcp)
    case [simp]: None
    from exec have execi: "(ta, xcp', h', frs') \<in> exec_instr (instrs_of (compP2 P) C M ! pc) (compP2 P) t h stk loc C M pc FRS"
      by(simp add: exec_1_iff)
    show ?thesis
    proof(cases "pc < length (compE2 body)")
      case True
      with execi sees' have execi: "(ta, xcp', h', frs') \<in> exec_instr (compE2 body ! pc) (compP2 P) t h stk loc C M pc FRS"
        by(simp)
      from \<tau> sees' True have \<tau>i: "\<tau>move2 (compP2 P) h stk body pc None" by(simp add: \<tau>move2_iff)

      show ?thesis
      proof(cases "length frs' = Suc (length FRS)")
        case False
        with execi sees True compE2_not_Return[of body]
        have "(\<exists>M n. compE2 body ! pc = Invoke M n)"
          apply(cases "compE2 body ! pc")
          apply(auto split: if_split_asm sum.split_asm simp add: split_beta compP2_def compMb2_def)
          apply(metis in_set_conv_nth)+
          done
        then obtain MM n where ins: "compE2 body ! pc = Invoke MM n" by blast
        with bisim1_Invoke_stkD[OF bisim[unfolded None], of MM n] True obtain vs' v' stk' 
          where [simp]: "stk = vs' @ v' # stk'" "n = length vs'" by auto
        from check sees True ins have "is_Ref v'"
          by(auto split: if_split_asm simp add: split_beta compP2_def compMb2_def check_def)
        moreover from execi sees True ins False sees' have "v' \<noteq> Null" by auto
        ultimately obtain a' where [simp]: "v' = Addr a'" by(auto simp add: is_Ref_def)
        from bisim have Bisim': "P,blocks1 0 (Class D#Ts) body,h \<turnstile> (e, xs) \<leftrightarrow> (rev (rev vs') @ Addr a' # stk', loc, pc, None)"
          by simp
        from bisim1_Invoke_\<tau>Red[OF this _ _ _ bsok, of MM t] True ins lenxs
        obtain e' xs' where red: "\<tau>red1r P t h (e, xs) (e', xs')"
          and bisim': "P,blocks1 0 (Class D#Ts) body,h \<turnstile> (e', xs') \<leftrightarrow> (rev (rev vs') @ Addr a' # stk', loc, pc, None)"
          and call': "call1 e' = \<lfloor>(a', MM, rev vs')\<rfloor>" by auto
        from red have Red: "\<tau>Red1r P t h ((e, xs), exs) ((e', xs'), exs)"
          by(rule \<tau>red1r_into_\<tau>Red1r)
        
        from False execi True check ins sees' obtain U' Ts' T' meth D'
          where ha': "typeof_addr h a' = \<lfloor>U'\<rfloor>"
          and Sees': "compP2 P \<turnstile> class_type_of U' sees MM:Ts' \<rightarrow> T' = \<lfloor>meth\<rfloor> in D'"
          by(auto simp add: check_def has_method_def split: if_split_asm)(auto split: extCallRet.split_asm)
        from sees_method_compPD[OF Sees'[unfolded compP2_def]] obtain body'
          where Sees: "P \<turnstile> class_type_of U' sees MM:Ts' \<rightarrow> T'=\<lfloor>body'\<rfloor> in D'"
          and [simp]: "meth = (max_stack body', max_vars body', compE2 body' @ [Return], compxE2 body' 0 0)"
          by(auto simp add: compMb2_def)
        
        let ?e = "blocks1 0 (Class D'#Ts') body'"
        let ?xs = "Addr a' # rev vs' @ replicate (max_vars body') undefined_value"
        let ?e'xs' = "(e', xs')"
        let ?f = "(stk, loc, C, M, pc)"
        let ?f' = "([],Addr a' # rev vs' @ replicate (max_vars body') undefined_value, D', MM, 0)"
        
        from execi pc ins False ha' Sees' sees'
        have [simp]: "xcp' = None" "ta = \<epsilon>" "frs' = ?f' # ?f # FRS" "h' = h"
          by(auto split: if_split_asm simp add: split_beta)
        
        from bisim' have bisim'': "P,blocks1 0 (Class D#Ts) body,h \<turnstile> (e', xs') \<leftrightarrow> (rev (rev vs') @ Addr a' # stk', loc, pc, None)"
          by simp
        have "n = length vs'" by simp
        from conf' Sees' ins sees' True have "n = length Ts'"
          apply(auto simp add: correct_state_def)
          apply(drule (1) sees_method_fun)+
          apply(auto dest: sees_method_idemp sees_method_fun)
          done
        with \<open>n = length vs'\<close> have vs'Ts': "length (rev vs') = length Ts'" by simp
        
        with call' ha' Sees
        have "True,P,t \<turnstile>1 \<langle>(e', xs')/exs,h\<rangle> -\<epsilon>\<rightarrow> \<langle>(?e, ?xs)/ (e', xs') # exs, h\<rangle>" by(rule red1Call)
        hence "True,P,t \<turnstile>1 \<langle>(e', xs')/exs,h\<rangle> -\<epsilon>\<rightarrow> \<langle>(?e, ?xs)/ ?e'xs' # exs, h\<rangle>" by(simp)
        moreover from call' Sees ha' have "\<tau>Move1 P h ((e', xs'), exs)"
          by(auto simp add: synthesized_call_def dest!: \<tau>move1_not_call1[where P=P and h=h] dest: sees_method_fun)
        ultimately have "\<tau>Red1t P t h ((e', xs'), exs) ((?e, ?xs), ?e'xs' # exs)" by auto
        moreover have "bisim1_list1 t h (?e, ?xs) (?e'xs' # exs) None (?f' # ?f # FRS)"
        proof
          from conf' show "compTP P \<turnstile> t:(None, h, ?f' # ?f # FRS) \<surd>" by simp
          from Sees show "P \<turnstile> D' sees MM: Ts'\<rightarrow>T' = \<lfloor>body'\<rfloor> in D'" by(rule sees_method_idemp)
          show "P,blocks1 0 (Class D'#Ts') body',h \<turnstile> (blocks1 0 (Class D'#Ts') body', ?xs) \<leftrightarrow> ([], Addr a' # rev vs' @ replicate (max_vars body') undefined_value, 0, None)"
            by(rule bisim1_refl)
          show "max_vars (blocks1 0 (Class D'#Ts') body') \<le> length ?xs" using vs'Ts' by(simp add: blocks1_max_vars)
          from sees have "bisim1_fr P h ?e'xs' ?f"
          proof
            show "P,blocks1 0 (Class D#Ts) body,h \<turnstile> (e', xs') \<leftrightarrow> (stk, loc, pc, None)"
              using bisim'' by simp
            from call' show "call1 e' = \<lfloor>(a', MM, rev vs')\<rfloor>" .
            from red have xs'xs: "length xs' = length xs" by(rule \<tau>red1r_preserves_len)
            with red lenxs show "max_vars e' \<le> length xs'" by(auto dest: \<tau>red1r_max_vars)
          qed
          with bisims show "list_all2 (bisim1_fr P h) (?e'xs' # exs) (?f # FRS)" by simp
        qed
        ultimately show ?thesis using Red
          by auto(blast intro: rtranclp_trans rtranclp_tranclp_tranclp tranclp_into_rtranclp)+
      next
        case True
        note pc = \<open>pc < length (compE2 body)\<close>
        with execi True have "\<exists>stk' loc' pc'. frs' = (stk', loc', C, M, pc') # FRS"
          by(cases "(compE2 body @ [Return]) ! pc")(auto split: if_split_asm sum.split_asm simp: split_beta, auto split: extCallRet.splits)
        then obtain stk' loc' pc' where [simp]: "frs' = (stk', loc', C, M, pc') # FRS" by blast
        from conf obtain ST where "compP2 P,h \<turnstile> stk [:\<le>] ST" by(auto simp add: correct_state_def conf_f_def2)
        hence ST: "P,h \<turnstile> stk [:\<le>] ST" by(rule List.list_all2_mono)(simp add: compP2_def)
        from execi sees pc check
        have exec': "exec_move_d P t (blocks1 0 (Class D#Ts) body) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
          apply(auto simp add: compP2_def compMb2_def exec_move_def check_def exec_meth_instr split: if_split_asm sum.split_asm)
          apply(cases "compE2 body ! pc")
          apply(auto simp add: neq_Nil_conv split_beta split: if_split_asm sum.split_asm)
          apply(force split: extCallRet.split_asm)
          apply(cases "compE2 body ! pc", auto simp add: split_beta neq_Nil_conv split: if_split_asm sum.split_asm)
          done
        from red1_simulates_exec_instr[OF wf hconf tconf bisim this _ bsok ST] lenxs \<tau>i obtain e'' xs''
          where bisim': "P,blocks1 0 (Class D#Ts) body,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
          and red: "(if xcp' = None \<longrightarrow> pc < pc' then \<tau>red1r else \<tau>red1t) P t h (e, xs) (e'', xs'')" and [simp]: "h' = h"
          by(auto simp del: blocks1.simps)
        have Red: "(if sim21_size (compP2 P) (xcp', frs') (xcp, frs) then \<tau>Red1r else \<tau>Red1t) P t h ((e, xs), exs) ((e'', xs''), exs)"
        proof(cases "xcp' = None \<longrightarrow> pc < pc'")
          case True
          from bisim bisim' have "pc \<le> Suc (length (compE2 body))" "pc' \<le> Suc (length (compE2 body))"
            by(auto dest: bisim1_pc_length_compE2)
          moreover {
            fix a assume "xcp' = \<lfloor>a\<rfloor>"
            with exec' have "pc = pc'" by(auto dest: exec_move_raise_xcp_pcD) }
          ultimately have "sim21_size (compP2 P) (xcp', frs') (xcp, frs)" using sees True 
            by(auto simp add: sim21_size_def)(auto simp add: compP2_def compMb2_def intro!: sim21_size_aux.intros)
          with red True show ?thesis by simp(rule \<tau>red1r_into_\<tau>Red1r)
        next
          case False
          thus ?thesis using red by(auto intro: \<tau>red1t_into_\<tau>Red1t \<tau>red1r_into_\<tau>Red1r)
        qed
        moreover from red lenxs
        have "max_vars e'' \<le> length xs''"
          apply(auto dest: \<tau>red1r_max_vars \<tau>red1r_preserves_len \<tau>red1t_max_vars \<tau>red1t_preserves_len split: if_split_asm)
          apply(frule \<tau>red1r_max_vars \<tau>red1t_max_vars, drule \<tau>red1r_preserves_len \<tau>red1t_preserves_len, simp)+
          done
        with conf' sees bisim'
        have "bisim1_list1 t h (e'', xs'') exs xcp' ((stk', loc', C, M, pc') # FRS)"
          unfolding \<open>frs' = (stk', loc', C, M, pc') # FRS\<close> \<open>h' = h\<close>
          using bisims by(rule bisim1_list1.bl1_Normal)
        ultimately show ?thesis by(auto split del: if_split)
      qed
    next
      case False
      with pc have [simp]: "pc = length (compE2 body)" by simp
      with execi sees have [simp]: "xcp' = None"
        by(cases "compE2 body ! pc")(auto split: if_split_asm simp add: compP2_def compMb2_def split_beta)
      from bisim have Bisim: "P,blocks1 0 (Class D#Ts) body,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, length (compE2 (blocks1 0 (Class D#Ts) body)), None)" by simp
      then obtain v where [simp]: "stk = [v]" by(blast dest: bisim1_pc_length_compE2D)
      with Bisim lenxs bsok have red: "\<tau>red1r P t h (e, xs) (Val v, loc)"
        by clarify (erule bisim1_Val_\<tau>red1r[where n=0], simp_all add: bsok_def)
      hence Red: "\<tau>Red1r P t h ((e, xs), exs) ((Val v, loc), exs)" by(rule \<tau>red1r_into_\<tau>Red1r)
      show ?thesis
      proof(cases "FRS")
        case [simp]: Nil
        with bisims have [simp]: "exs = []" by simp
        with exec sees' have [simp]: "ta = \<epsilon>" "xcp' = None" "h' = h" "frs' = []"
          by(auto simp add: exec_1_iff)
        from hconf have "bisim1_list1 t h (Val v, loc) [] None []" by(rule bl1_finalVal)
        then show ?thesis using Red
          by(auto intro: rtranclp.rtrancl_into_rtrancl rtranclp_into_tranclp1 simp del: \<tau>Red1_conv simp add: sim21_size_def)
      next
        case (Cons f' FRS')
        then obtain stk'' loc'' C'' M'' pc''
          where [simp]: "FRS = (stk'', loc'', C'', M'', pc'') # FRS'" by(cases f') fastforce
        from bisims obtain e'' xs'' EXS' where [simp]: "exs = (e'', xs'') # EXS'"
          by(auto simp add: list_all2_Cons2)
        with bisims have "bisim1_fr P h (e'', xs'') (stk'', loc'', C'', M'', pc'')" by simp
        then obtain E'' Ts'' T'' body'' D'' a'' M''' vs''
          where [simp]: "e'' = E''"
          and sees'': "P \<turnstile> C'' sees M'':Ts''\<rightarrow>T'' = \<lfloor>body''\<rfloor> in D''"
          and bisim'': "P,blocks1 0 (Class D''#Ts'') body'',h \<turnstile> (E'', xs'') \<leftrightarrow> (stk'', loc'', pc'', None)"
          and call'': "call1 E'' =  \<lfloor>(a'', M''', vs'')\<rfloor>"
          and lenxs'': "max_vars E'' \<le> length xs''"
          by(cases) fastforce
        let ?ee' = "inline_call (Val v) E''"
        let ?e' = "?ee'"
        let ?xs' = "xs''"
          
        from bisim'' call'' have pc'': "pc'' < length (compE2 (blocks1 0 (Class D''#Ts'') body''))"
          by(rule bisim1_call_pcD)
        hence pc'': "pc'' < length (compE2 body'')" by simp
        with sees_method_compP[OF sees'', where f="\<lambda>C M Ts T. compMb2"] 
          sees_method_compP[OF sees, where f="\<lambda>C M Ts T. compMb2"] conf
        obtain ST LT where \<Phi>: "compTP P C'' M'' ! pc'' = \<lfloor>(ST, LT)\<rfloor>"
          and conff: "conf_f (compP (\<lambda>C M Ts T. compMb2) P) h (ST, LT) (compE2 body'' @ [Return]) (stk'', loc'', C'', M'', pc'')"
          and ins: "(compE2 body'' @ [Return]) ! pc'' = Invoke M (length Ts)"
          unfolding correct_state_def by(fastforce simp add: compP2_def compMb2_def dest: sees_method_fun)
        from bisim1_callD[OF bisim'' call'', of M "length Ts"] ins pc''
        have [simp]: "M''' = M" by simp
          
        from call'' have "call1 E'' = \<lfloor>(a'', M''', vs'')\<rfloor>" by simp
        have "True,P,t \<turnstile>1 \<langle>(Val v, loc)/(E'', xs'') # EXS',h\<rangle> -\<epsilon>\<rightarrow>
                      \<langle>(inline_call (Val v) E'', xs'')/EXS', h\<rangle>"
          by(rule red1Return) simp
        hence "True,P,t \<turnstile>1 \<langle>(Val v, loc)/(E'', xs'') # EXS',h\<rangle> -\<epsilon>\<rightarrow> \<langle>(?e', ?xs')/EXS', h\<rangle>"
          by simp
        moreover have "\<tau>Move1 P h ((Val v, loc), (E'', xs'') # EXS')" by auto
        ultimately have "\<tau>Red1 P t h ((Val v, loc), (E'', xs'') # EXS') ((?e', ?xs'), EXS')" by auto
        moreover from exec sees have [simp]: "ta = \<epsilon>" "h' = h"
          and [simp]: "frs' = (v # drop (length Ts + 1) stk'', loc'', C'', M'', pc'' + 1) # FRS'"
          by(auto simp add: compP2_def compMb2_def exec_1_iff)
          
        have "bisim1_list1 t h (?e', ?xs') EXS' None ((v # drop (length Ts + 1) stk'', loc'', C'', M'', pc'' + 1) # FRS')"
        proof
          from conf' show "compTP P \<turnstile> t: (None, h, (v # drop (length Ts + 1) stk'', loc'', C'', M'', pc'' + 1) # FRS') \<surd>" by simp
          from sees'' show "P \<turnstile> C'' sees M'': Ts''\<rightarrow>T'' = \<lfloor>body''\<rfloor> in D''" .
          from bisim1_inline_call_Val[OF bisim'' call'', of "length Ts" v] ins pc''
          show "P,blocks1 0 (Class D''#Ts'') body'',h \<turnstile> (inline_call (Val v) E'', xs'') \<leftrightarrow> (v # drop (length Ts + 1) stk'', loc'', pc'' + 1, None)" by simp
          from lenxs'' max_vars_inline_call[of "Val v" "E''"]
          show "max_vars (inline_call (Val v) E'') \<le> length xs''" by simp
          from bisims show "list_all2 (bisim1_fr P h) EXS' FRS'" by simp
        qed
        ultimately show ?thesis using Red
          by(auto simp del: \<tau>Red1_conv intro: rtranclp_into_tranclp1 rtranclp.rtrancl_into_rtrancl)
      qed
    qed
  next
    case [simp]: (Some a')
    from exec have execs: "(xcp', h', frs') = exception_step (compP2 P) a' h (stk, loc, C, M, pc) FRS"
      and [simp]: "ta = \<epsilon>" by(auto simp add: exec_1_iff)
    from conf have confxcp': "conf_xcp' P h xcp" 
      unfolding correct_state_def by(auto simp add: compP2_def)
    then obtain D' where ha': "typeof_addr h a' = \<lfloor>Class_type D'\<rfloor>" and subclsD': "P \<turnstile> D' \<preceq>\<^sup>* Throwable" by auto
    from bisim have pc: "pc < length (compE2 body)" by(auto dest: bisim1_xcp_pcD)
    show ?thesis
    proof(cases "match_ex_table (compP2 P) (cname_of h a') pc (ex_table_of (compP2 P) C M)")
      case None
      from bisim have pc: "pc < length (compE2 body)" by(auto dest: bisim1_xcp_pcD)
      with sees' None have match: "match_ex_table (compP2 P) (cname_of h a') pc (compxE2 body 0 0) = None"
        by(auto)
      with execs sees' have [simp]: "ta = \<epsilon>" "xcp' = \<lfloor>a'\<rfloor>" "h' = h" "frs' = FRS" using match sees' by auto
      from conf obtain CCC where ha: "typeof_addr h a' = \<lfloor>Class_type CCC\<rfloor>" and subcls: "P \<turnstile> CCC \<preceq>\<^sup>* Throwable"
        unfolding correct_state_def by(auto simp add: conf_f_def2 compP2_def)
      from bisim1_xcp_\<tau>Red[OF ha subcls bisim[unfolded Some], of "\<lambda>C M Ts T. compMb2"] match lenxs bsok
      have red: "\<tau>red1r P t h (e, xs) (Throw a', loc)"
        and b': "P,blocks1 0 (Class D#Ts) body,h \<turnstile> (Throw a', loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)"
        by(auto simp add: compP2_def bsok_def)
      from red have Red: "\<tau>Red1r P t h ((e, xs), exs) ((Throw a', loc), exs)"
        by(rule \<tau>red1r_into_\<tau>Red1r)
      show ?thesis
      proof(cases "FRS")
        case (Cons f' FRS')
        then obtain stk'' loc'' C'' M'' pc''
          where [simp]: "FRS = (stk'', loc'', C'', M'', pc'') # FRS'" by(cases f') fastforce
        from bisims obtain e'' xs'' EXS' where [simp]: "exs = (e'', xs'') # EXS'" 
          by(auto simp add: list_all2_Cons2)
        with bisims have "bisim1_fr P h (e'', xs'') (stk'', loc'', C'', M'', pc'')" by simp
        then obtain E'' Ts'' T'' body'' D'' a'' M''' vs''
          where [simp]: "e'' = E''"
          and sees'': "P \<turnstile> C'' sees M'':Ts''\<rightarrow>T'' = \<lfloor>body''\<rfloor> in D''"
          and bisim'': "P,blocks1 0 (Class D''#Ts'') body'',h \<turnstile> (E'', xs'') \<leftrightarrow> (stk'', loc'', pc'', None)"
          and call'': "call1 E'' =  \<lfloor>(a'', M''', vs'')\<rfloor>"
          and lenxs'': "max_vars E'' \<le> length xs''"
          by(cases) fastforce
        let ?ee' = "inline_call (Throw a') E''"
        let ?e' = "?ee'"
        let ?xs' = "xs''"
          
        from bisim'' call'' have pc'': "pc'' < length (compE2 (blocks1 0 (Class D''#Ts'') body''))"
          by(rule bisim1_call_pcD)
        hence pc'': "pc'' < length (compE2 body'')" by simp
        with sees_method_compP[OF sees'', where f="\<lambda>C M Ts T. compMb2"]
          sees_method_compP[OF sees, where f="\<lambda>C M Ts T. compMb2"] conf
        obtain ST LT where \<Phi>: "compTP P C'' M'' ! pc'' = \<lfloor>(ST, LT)\<rfloor>"
          and conff: "conf_f (compP (\<lambda>C M Ts T. compMb2) P) h (ST, LT) (compE2 body'' @ [Return]) (stk'', loc'', C'', M'', pc'')"
          and ins: "(compE2 body'' @ [Return]) ! pc'' = Invoke M (length Ts)"
          unfolding correct_state_def
          by(fastforce simp add: compP2_def compMb2_def dest: sees_method_fun)
        from bisim1_callD[OF bisim'' call'', of M "length Ts"] ins pc''
        have [simp]: "M''' = M" by simp
        
        have "True,P,t \<turnstile>1 \<langle>(Throw a', loc)/(E'', xs'') # EXS',h\<rangle> -\<epsilon>\<rightarrow> \<langle>(inline_call (Throw a') E'', xs'')/EXS', h\<rangle>"
          by(rule red1Return) simp
        moreover have "\<tau>Move1 P h ((Throw a', loc), (E'', xs'') # EXS')" by fastforce
        ultimately have "\<tau>Red1 P t h ((Throw a', loc), (E'', xs'') # EXS') ((?e', ?xs'), EXS')" by simp
        moreover
        have "bisim1_list1 t h (?e', ?xs') EXS' \<lfloor>a'\<rfloor> ((stk'', loc'', C'', M'', pc'') # FRS')"
        proof
          from conf' show "compTP P \<turnstile> t: (\<lfloor>a'\<rfloor>, h, (stk'', loc'', C'', M'', pc'') # FRS') \<surd>" by simp
          from sees'' show "P \<turnstile> C'' sees M'': Ts''\<rightarrow>T'' = \<lfloor>body''\<rfloor> in D''" .
          from bisim1_inline_call_Throw[OF bisim'' call'', of "length Ts" a'] ins pc''
          show "P,blocks1 0 (Class D''#Ts'') body'',h \<turnstile> (inline_call (Throw a') E'', xs'') \<leftrightarrow> (stk'', loc'', pc'', \<lfloor>a'\<rfloor>)"
            by simp
          from lenxs'' max_vars_inline_call[of "Throw a'" "E''"]
          show "max_vars (inline_call (Throw a') E'') \<le> length xs''" by simp
          from bisims show "list_all2 (bisim1_fr P h) EXS' FRS'" by simp
        qed
        ultimately show ?thesis using Red
          by(auto simp del: \<tau>Red1_conv intro: rtranclp.rtrancl_into_rtrancl rtranclp_into_tranclp1)
      next
        case [simp]: Nil
        with bisims have [simp]: "exs = []" by simp
        from hconf have "bisim1_list1 t h (Throw a', loc) [] \<lfloor>a'\<rfloor> []" by(rule bl1_finalThrow)
        thus ?thesis using Red 
          by(auto simp del: \<tau>Red1_conv intro: rtranclp.rtrancl_into_rtrancl rtranclp_into_tranclp1 simp add: sim21_size_def)
      qed
    next
      case (Some pcd)
      then obtain pch d where match: "match_ex_table (compP2 P) (cname_of h a') pc (ex_table_of (compP2 P) C M) = \<lfloor>(pch, d)\<rfloor>"
        by(cases pcd) auto
      with \<tau> sees' pc have \<tau>': "\<tau>move2 (compP2 P) h stk body pc \<lfloor>a'\<rfloor>" by(simp add: compP2_def compMb2_def \<tau>move2_iff)
      from match execs have [simp]: "h' = h" "xcp' = None" 
        "frs' = (Addr a' # drop (length stk - d) stk, loc, C, M, pch) # FRS" by simp_all
      from bisim match sees'
      have "d \<le> length stk" by(auto intro: bisim1_match_Some_stk_length simp add: compP2_def compMb2_def)
      with match sees'
      have execm: "exec_move_d P t (blocks1 0 (Class D#Ts) body) h (stk, loc, pc, \<lfloor>a'\<rfloor>) ta h' (Addr a' # drop (length stk - d) stk, loc, pch, None)"
        by(auto simp add: exec_move_def exec_meth_xcpt)
      from conf obtain ST where "compP2 P,h \<turnstile> stk [:\<le>] ST" by(auto simp add: correct_state_def conf_f_def2)
      hence ST: "P,h \<turnstile> stk [:\<le>] ST" by(rule List.list_all2_mono)(simp add: compP2_def)
      from red1_simulates_exec_instr[OF wf hconf tconf bisim[unfolded \<open>xcp = \<lfloor>a'\<rfloor>\<close>] execm _ bsok ST] lenxs ha' subclsD' \<tau>'
      obtain e'' xs''
        where b': "P,blocks1 0 (Class D#Ts) body,h \<turnstile> (e'', xs'') \<leftrightarrow> (Addr a' # drop (length stk - d) stk, loc, pch, None)"
        and red: "(if pc < pch then \<tau>red1r else \<tau>red1t) P t h (e, xs) (e'', xs'')" and [simp]: "h' = h"
        by(auto split: if_split_asm intro: \<tau>move2xcp simp add: compP2_def simp del: blocks1.simps)
      have Red: "(if sim21_size (compP2 P) (xcp', frs') (xcp, frs) then \<tau>Red1r else \<tau>Red1t) P t h ((e, xs), exs) ((e'', xs''), exs)"
      proof(cases "pc < pch")
        case True
        from bisim b' have "pc \<le> Suc (length (compE2 body))" "pch \<le> Suc (length (compE2 body))"
          by(auto dest: bisim1_pc_length_compE2)
        with sees True have "sim21_size (compP2 P) (xcp', frs') (xcp, frs)"
          by(auto simp add: sim21_size_def)(auto simp add: compP2_def compMb2_def intro: sim21_size_aux.intros)
        with red True show ?thesis by simp(rule \<tau>red1r_into_\<tau>Red1r)
      next
        case False
        thus ?thesis using red by(auto intro: \<tau>red1t_into_\<tau>Red1t \<tau>red1r_into_\<tau>Red1r)
      qed
      moreover from red lenxs
      have "max_vars e'' \<le> length xs''"
        apply(auto dest: \<tau>red1r_max_vars \<tau>red1r_preserves_len \<tau>red1t_max_vars \<tau>red1t_preserves_len split: if_split_asm)
        apply(frule \<tau>red1r_max_vars \<tau>red1t_max_vars, drule \<tau>red1r_preserves_len \<tau>red1t_preserves_len, simp)+
        done
      with conf' sees b'
      have "bisim1_list1 t h (e'', xs'') exs None ((Addr a' # drop (length stk - d) stk, loc, C, M, pch) # FRS)"
        using bisims unfolding \<open>h' = h\<close> \<open>xcp' = None\<close>
          \<open>frs' = (Addr a' # drop (length stk - d) stk, loc, C, M, pch) # FRS\<close>
        by rule
      ultimately show ?thesis by(auto split del: if_split)
    qed
  qed
qed(insert exec, auto simp add: exec_1_iff elim!: jvmd_NormalE)

lemma \<tau>Red1_simulates_exec_1_not_\<tau>:
  assumes wf: "wf_J1_prog P"
  and exec: "exec_1_d (compP2 P) t (Normal (xcp, h, frs)) ta (Normal (xcp', h', frs'))"
  and bisim: "bisim1_list1 t h (e, xs) exs xcp frs"
  and \<tau>: "\<not> \<tau>Move2 (compP2 P) (xcp, h, frs)"
  shows "\<exists>e' xs' exs' ta' e'' xs'' exs''. \<tau>Red1r P t h ((e, xs), exs) ((e', xs'), exs') \<and>
                                      True,P,t \<turnstile>1 \<langle>(e', xs')/exs', h\<rangle> -ta'\<rightarrow> \<langle>(e'', xs'')/exs'', h'\<rangle> \<and>
                                      \<not> \<tau>Move1 P h ((e', xs'), exs') \<and> ta_bisim wbisim1 ta' ta \<and>
                                      bisim1_list1 t h' (e'', xs'') exs'' xcp' frs' \<and> 
                                      (call1 e = None \<or>
                                      (case frs of Nil \<Rightarrow> False | (stk, loc, C, M, pc) # FRS \<Rightarrow> \<forall>M' n. instrs_of (compP2 P) C M ! pc \<noteq> Invoke M' n) \<or>
                                       e' = e \<and> xs' = xs \<and> exs' = exs)
"
using bisim
proof cases
  case (bl1_Normal stk loc C M pc FRS Ts T body D)
  hence [simp]: "frs = (stk, loc, C, M, pc) # FRS"
    and conf: "compTP P \<turnstile> t: (xcp, h, (stk, loc, C, M, pc) # FRS) \<surd>"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>body\<rfloor> in D"
    and bisim: "P,blocks1 0 (Class D#Ts) body,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
    and lenxs: "max_vars e \<le> length xs"
    and bisims: "list_all2 (bisim1_fr P h) exs FRS" by auto

  from sees_method_compP[OF sees, where f="\<lambda>C M Ts T. compMb2"]
  have sees': "compP2 P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>(max_stack body, max_vars body, compE2 body @ [Return], compxE2 body 0 0)\<rfloor> in D"
    by(simp add: compP2_def compMb2_def)
  from bisim have pc: "pc \<le> length (compE2 body)" by(auto dest: bisim1_pc_length_compE2)
  from conf have hconf: "hconf h" "preallocated h" and tconf: "P,h \<turnstile> t \<surd>t"
    unfolding correct_state_def by(simp_all add: compP2_def tconf_def)

  from sees wf have bsok: "bsok (blocks1 0 (Class D # Ts) body) 0"
    by(auto dest!: sees_wf_mdecl simp add: bsok_def wf_mdecl_def WT1_expr_locks)

  from exec obtain check: "check (compP2 P) (xcp, h, frs)"
    and exec: "compP2 P,t \<turnstile> (xcp, h, frs) -ta-jvm\<rightarrow> (xcp', h', frs')"
    by(rule jvmd_NormalE)(auto simp add: exec_1_iff)

  from wt_compTP_compP2[OF wf] exec conf
  have conf': "compTP P \<turnstile> t: (xcp', h', frs') \<surd>" by(auto intro: BV_correct_1)

  show ?thesis
  proof(cases xcp)
    case [simp]: None
    from exec have execi: "(ta, xcp', h', frs') \<in> exec_instr (instrs_of (compP2 P) C M ! pc) (compP2 P) t h stk loc C M pc FRS"
      by(simp add: exec_1_iff)
    show ?thesis
    proof(cases "length frs' = Suc (length FRS)")
      case True
      with pc execi sees' have pc: "pc < length (compE2 body)"
        by(auto split: if_split_asm simp add: split_beta)
      with execi sees' have execi: "(ta, xcp', h', frs') \<in> exec_instr (compE2 body ! pc) (compP2 P) t h stk loc C M pc FRS"
        by(simp)
      from \<tau> sees' True pc have \<tau>i: "\<not> \<tau>move2 (compP2 P) h stk body pc None" by(simp add: \<tau>move2_iff)
      from execi True sees' pc have "\<exists>stk' loc' pc'. frs' = (stk', loc', C, M, pc') # FRS"
        by(cases "(compE2 body @ [Return]) ! pc")(auto split: if_split_asm sum.split_asm simp add: split_beta, auto split: extCallRet.splits)
      then obtain stk' loc' pc' where [simp]: "frs' = (stk', loc', C, M, pc') # FRS" by blast
      from conf obtain ST where "compP2 P,h \<turnstile> stk [:\<le>] ST" by(auto simp add: correct_state_def conf_f_def2)
      hence ST: "P,h \<turnstile> stk [:\<le>] ST" by(rule List.list_all2_mono)(simp add: compP2_def)
      from execi sees True check pc
      have exec': "exec_move_d P t (blocks1 0 (Class D#Ts) body) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
        apply(auto simp add: compP2_def compMb2_def exec_move_def check_def exec_meth_instr split: if_split_asm sum.split_asm)
        apply(cases "compE2 body ! pc")
        apply(auto simp add: neq_Nil_conv split_beta split: if_split_asm sum.split_asm)
        apply(force split: extCallRet.split_asm)
        apply(cases "compE2 body ! pc", auto simp add: split_beta neq_Nil_conv split: if_split_asm sum.split_asm)
        done
      from red1_simulates_exec_instr[OF wf hconf tconf bisim this _ bsok ST] lenxs \<tau>i obtain e'' xs'' ta' e' xs'
        where bisim': "P,blocks1 0 (Class D#Ts) body,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
        and red1: "\<tau>red1r P t h (e, xs) (e', xs')" and red2: "True,P,t \<turnstile>1 \<langle>e',(h, xs')\<rangle> -ta'\<rightarrow> \<langle>e'',(h', xs'')\<rangle>"
        and \<tau>1: "\<not> \<tau>move1 P h e'" and tabisim: "ta_bisim wbisim1 (extTA2J1 P ta') ta" 
        and call: "call1 e = None \<or> no_call2 (blocks1 0 (Class D # Ts) body) pc \<or> e' = e \<and> xs' = xs"
        by(fastforce simp del: blocks1.simps)
      from red1 have Red1: "\<tau>Red1r P t h ((e, xs), exs) ((e', xs'), exs)"
        by(rule \<tau>red1r_into_\<tau>Red1r)
      moreover from red2 have "True,P,t \<turnstile>1 \<langle>(e', xs')/exs, h\<rangle> -extTA2J1 P ta'\<rightarrow> \<langle>(e'', xs'')/exs, h'\<rangle>"
        by(rule red1Red)
      moreover from \<tau>1 red2 have "\<not> \<tau>Move1 P h ((e', xs'), exs)" by auto
      moreover from \<tau>red1r_max_vars[OF red1] lenxs \<tau>red1r_preserves_len[OF red1]
      have "max_vars e' \<le> length xs'" by simp
      with red1_preserves_len[OF red2] red1_max_vars[OF red2]
      have "max_vars e'' \<le> length xs''" by simp
      with conf' sees bisim'
      have "bisim1_list1 t h' (e'', xs'') exs xcp' ((stk', loc', C, M, pc') # FRS)"
        unfolding \<open>frs' = (stk', loc', C, M, pc') # FRS\<close>
      proof
        from red2 have "hext h h'" by(auto dest: red1_hext_incr)
        from bisims show "list_all2 (bisim1_fr P h') exs FRS"
          by(rule List.list_all2_mono)(erule bisim1_fr_hext_mono[OF _ \<open>hext h h'\<close>])
      qed
      moreover from call sees'
      have "call1 e = None \<or> (\<forall>M' n. instrs_of (compP2 P) C M ! pc \<noteq> Invoke M' n) \<or> e' = e \<and> xs' = xs"
        by(auto simp add: no_call2_def)
      ultimately show ?thesis using tabisim
        by(fastforce simp del: split_paired_Ex)
    next
      case False
      with execi sees pc compE2_not_Return[of body]
      have "(pc = length (compE2 body) \<or> (\<exists>M n. compE2 body ! pc = Invoke M n)) \<and> xcp' = None"
        apply(cases "compE2 body ! pc")
        apply(auto split: if_split_asm sum.split_asm simp add: split_beta compP2_def compMb2_def)
        apply(auto split: extCallRet.splits)
        apply(metis in_set_conv_nth)+
        done
      hence [simp]: "xcp' = None"
        and "pc = length (compE2 body) \<or> (\<exists>M n. compE2 body ! pc = Invoke M n)" by simp_all
      moreover
      { assume [simp]: "pc = length (compE2 body)"
        with sees_method_compP[OF sees, where f="\<lambda>C M Ts T. compMb2"] \<tau> have False by(auto simp add: compMb2_def compP2_def)
        hence ?thesis .. }
      moreover {
        assume "\<exists>M n. compE2 body ! pc = Invoke M n"
          and "pc \<noteq> length (compE2 body)"
        with pc obtain MM n where ins: "compE2 body ! pc = Invoke MM n"
          and pc: "pc < length (compE2 body)" by auto
        with bisim1_Invoke_stkD[OF bisim[unfolded None], of MM n] obtain vs' v' stk' 
          where [simp]: "stk = vs' @ v' # stk'" "n = length vs'" by auto
        with False \<tau> sees' execi pc ins have False by auto (auto split: extCallRet.split_asm) }
      ultimately show ?thesis by blast
    qed
  next
    case [simp]: (Some ad)
    from bisim have pc: "pc < length (compE2 body)" by(auto dest: bisim1_xcp_pcD)
    with \<tau> sees' have False by auto
    thus ?thesis ..
  qed
qed(insert exec, auto simp add: exec_1_iff elim!: jvmd_NormalE)

end

end
