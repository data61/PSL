(*  Title:      JinjaThreads/MM/JMM_Common.thy
    Author:     Andreas Lochbihler
*)

section \<open>JMM Instantiation with Jinja -- common parts\<close>

theory JMM_Common
imports
  JMM_Framework
  JMM_Typesafe
  "../Common/BinOp"
  "../Common/ExternalCallWF"
begin

context heap begin

lemma heap_copy_loc_not_New: assumes "heap_copy_loc a a' al h ob h'"
  shows "NewHeapElem a'' x \<in> set ob \<Longrightarrow> False"
using assms
by(auto elim: heap_copy_loc.cases)

lemma heap_copies_not_New:
  assumes "heap_copies a a' als h obs h'" 
  and "NewHeapElem a'' x \<in> set obs"
  shows "False"
using assms
by induct(auto dest: heap_copy_loc_not_New)

lemma heap_clone_New_same_addr_same:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "obs ! i = NewHeapElem a'' x" "i < length obs"
  and "obs ! j = NewHeapElem a'' x'" "j < length obs"
  shows "i = j"
using assms
apply cases
apply(fastforce simp add: nth_Cons' gr0_conv_Suc in_set_conv_nth split: if_split_asm dest: heap_copies_not_New)+
done

lemma red_external_New_same_addr_same:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; 
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a' x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a' x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
by(auto elim!: red_external.cases simp add: nth_Cons' split: if_split_asm dest: heap_clone_New_same_addr_same)

lemma red_external_aggr_New_same_addr_same:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h;
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a' x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
    \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a' x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
by(auto simp add: external_WT_defs.simps red_external_aggr_def nth_Cons' split: if_split_asm if_split_asm dest: heap_clone_New_same_addr_same)

lemma heap_copy_loc_read_typeable:
  assumes "heap_copy_loc a a' al h obs h'"
  and "ReadMem ad al' v \<in> set obs"
  and "P,h \<turnstile> a@al : T"
  shows "ad = a \<and> al'= al"
using assms by cases auto

lemma heap_copies_read_typeable:
  assumes "heap_copies a a' als h obs h'"
  and "ReadMem ad al' v \<in> set obs"
  and "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts"
  shows "ad = a \<and> al' \<in> set als"
using assms
proof(induct arbitrary: Ts)
  case Nil thus ?case by simp
next
  case (Cons al h ob h' als obs h'')
  from \<open>list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) (al # als) Ts\<close>
  obtain T Ts' where Ts [simp]: "Ts = T # Ts'"
    and "P,h \<turnstile> a@al : T" 
    and "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)
  from \<open>ReadMem ad al' v \<in> set (ob @ obs)\<close>
  show ?case unfolding set_append Un_iff
  proof
    assume "ReadMem ad al' v \<in> set ob"
    with \<open>heap_copy_loc a a' al h ob h'\<close>
    have "ad = a \<and> al'= al" using \<open>P,h \<turnstile> a@al : T\<close>
      by(rule heap_copy_loc_read_typeable)
    thus ?thesis by simp
  next
    assume "ReadMem ad al' v \<in> set obs"
    moreover from \<open>heap_copy_loc a a' al h ob h'\<close>
    have "h \<unlhd> h'" by(rule hext_heap_copy_loc)
    from \<open>list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts'\<close>
    have "list_all2 (\<lambda>al T. P,h' \<turnstile> a@al : T) als Ts'"
      by(rule List.list_all2_mono)(rule addr_loc_type_hext_mono[OF _ \<open>h \<unlhd> h'\<close>])
    ultimately have "ad = a \<and> al' \<in> set als" by(rule Cons)
    thus ?thesis by simp
  qed
qed

lemma heap_clone_read_typeable:
  assumes clone: "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and read: "ReadMem ad al v \<in> set obs"
  shows "ad = a \<and> (\<exists>T'. P,h \<turnstile> ad@al : T')"
using clone
proof cases
  case (ObjClone C H' FDTs obs')
  let ?als = "map (\<lambda>((F, D), Tm). CField D F) FDTs"
  let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs"
  note \<open>heap_copies a a' ?als H' obs' h'\<close>
  moreover
  from \<open>obs = NewHeapElem a' (Class_type C) # obs'\<close> read 
  have "ReadMem ad al v \<in> set obs'" by simp
  moreover
  from \<open>(H', a') \<in> allocate h (Class_type C)\<close> have "h \<unlhd> H'" by(rule hext_allocate)
  hence "typeof_addr H' a = \<lfloor>Class_type C\<rfloor>" using \<open>typeof_addr h a = \<lfloor>Class_type C\<rfloor>\<close>
    by(rule typeof_addr_hext_mono)
  hence type: "list_all2 (\<lambda>al T. P,H' \<turnstile> a@al : T) ?als ?Ts"
    using \<open>P \<turnstile> C has_fields FDTs\<close>
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastforce intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
  ultimately have "ad = a \<and> al \<in> set ?als" by(rule heap_copies_read_typeable)
  hence [simp]: "ad = a" and "al \<in> set ?als" by simp_all
  then obtain F D T where [simp]: "al = CField D F" and "((F, D), T) \<in> set FDTs" by auto
  with type \<open>h \<unlhd> H'\<close> \<open>typeof_addr h a = \<lfloor>Class_type C\<rfloor>\<close> show ?thesis 
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastforce elim!: ballE[where x="((F, D), T)"] addr_loc_type.cases dest: typeof_addr_hext_mono intro: addr_loc_type.intros)
next
  case (ArrClone T n H' FDTs obs')
  let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<n]"
  let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs @ replicate n T"
  note FDTs = \<open>P \<turnstile> Object has_fields FDTs\<close>
  note \<open>heap_copies a a' ?als H' obs' h'\<close>
  moreover from \<open>obs = NewHeapElem a' (Array_type T n) # obs'\<close> read
  have "ReadMem ad al v \<in> set obs'" by simp
  moreover from \<open>(H', a') \<in> allocate h (Array_type T n)\<close>
  have "h \<unlhd> H'" by(rule hext_allocate)
  with \<open>typeof_addr h a = \<lfloor>Array_type T n\<rfloor>\<close>
  have type': "typeof_addr H' a = \<lfloor>Array_type T n\<rfloor>"
    by(auto dest: typeof_addr_hext_mono hext_arrD)
  hence type: "list_all2 (\<lambda>al T. P,H' \<turnstile> a@al : T) ?als ?Ts" using FDTs
    by(fastforce intro: list_all2_all_nthI addr_loc_type.intros simp add: has_field_def list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv dest: weak_map_of_SomeI)
  ultimately have "ad = a \<and> al \<in> set ?als" by(rule heap_copies_read_typeable)
  hence [simp]: "ad = a" and "al \<in> set ?als" by simp_all
  hence "al \<in> set (map (\<lambda>((F, D), Tfm). CField D F) FDTs) \<or> al \<in> set (map ACell [0..<n])" by simp
  thus ?thesis
  proof
    assume "al \<in> set (map (\<lambda>((F, D), Tfm). CField D F) FDTs)"
    then obtain F D Tfm where [simp]: "al = CField D F" and "((F, D), Tfm) \<in> set FDTs" by auto
    with type type' \<open>h \<unlhd> H'\<close> \<open>typeof_addr h a = \<lfloor>Array_type T n\<rfloor>\<close> show ?thesis 
      by(fastforce elim!: ballE[where x="((F, D), Tfm)"] addr_loc_type.cases intro: addr_loc_type.intros simp add: list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv)
  next
    assume "al \<in> set (map ACell [0..<n])"
    then obtain n' where [simp]: "al = ACell n'" and "n' < n" by auto
    with type type' \<open>h \<unlhd> H'\<close> \<open>typeof_addr h a = \<lfloor>Array_type T n\<rfloor>\<close>
    show ?thesis by(fastforce dest: list_all2_nthD[where p=n'] elim: addr_loc_type.cases intro: addr_loc_type.intros)
  qed
qed

lemma red_external_read_mem_typeable:
  assumes red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and read: "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "\<exists>T'. P,h \<turnstile> ad@al : T'"
using red read
by cases(fastforce dest: heap_clone_read_typeable intro: addr_loc_type.intros)+

end

context heap_conf begin

lemma heap_clone_typeof_addrD:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "hconf h"
  shows "NewHeapElem a'' x \<in> set obs \<Longrightarrow> a'' = a' \<and> typeof_addr h' a' = Some x"
using assms
by(fastforce elim!: heap_clone.cases dest: allocate_SomeD hext_heap_copies heap_copies_not_New typeof_addr_is_type elim: hext_objD hext_arrD)

lemma red_external_New_typeof_addrD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewHeapElem a' x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; hconf h \<rbrakk>
  \<Longrightarrow> typeof_addr h' a' = Some x"
by(erule red_external.cases)(auto dest: heap_clone_typeof_addrD)

lemma red_external_aggr_New_typeof_addrD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; NewHeapElem a' x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     is_native P (the (typeof_addr h a)) M; hconf h \<rbrakk>
  \<Longrightarrow> typeof_addr h' a' = Some x"
apply(auto simp add: is_native.simps external_WT_defs.simps red_external_aggr_def split: if_split_asm)
apply(blast dest: heap_clone_typeof_addrD)+
done

end

context heap_conf begin

lemma heap_copy_loc_non_speculative_typeable:
  assumes copy: "heap_copy_loc ad ad' al h obs h'"
  and sc: "non_speculative P vs (llist_of (map NormalAction obs))"
  and vs: "vs_conf P h vs"
  and hconf: "hconf h"
  and wt: "P,h \<turnstile> ad@al : T" "P,h \<turnstile> ad'@al : T"
  shows "heap_base.heap_copy_loc (heap_read_typed P) heap_write ad ad' al h obs h'"
proof -
  from copy obtain v where obs: "obs = [ReadMem ad al v, WriteMem ad' al v]"
    and read: "heap_read h ad al v" and "write": "heap_write h ad' al v h'" by cases
  from obs sc have "v \<in> vs (ad, al)" by auto
  with vs wt have v: "P,h \<turnstile> v :\<le> T" by(blast dest: vs_confD addr_loc_type_fun)+
  with read wt have "heap_read_typed P h ad al v"
    by(auto intro: heap_read_typedI dest: addr_loc_type_fun)
  thus ?thesis using "write" unfolding obs by(rule heap_base.heap_copy_loc.intros)
qed

lemma heap_copy_loc_non_speculative_vs_conf:
  assumes copy: "heap_copy_loc ad ad' al h obs h'"
  and sc: "non_speculative P vs (llist_of (take n (map NormalAction obs)))"
  and vs: "vs_conf P h vs"
  and hconf: "hconf h"
  and wt: "P,h \<turnstile> ad@al : T" "P,h \<turnstile> ad'@al : T"
  shows "vs_conf P h' (w_values P vs (take n (map NormalAction obs)))"
proof -
  from copy obtain v where obs: "obs = [ReadMem ad al v, WriteMem ad' al v]"
    and read: "heap_read h ad al v" and "write": "heap_write h ad' al v h'" by cases
  from "write" have hext: "h \<unlhd> h'" by(rule hext_heap_write)
  with vs have vs': "vs_conf P h' vs" by(rule vs_conf_hext)
  show ?thesis
  proof(cases "n > 0")
    case True
    with obs sc have "v \<in> vs (ad, al)" by(auto simp add: take_Cons')
    with vs wt have v: "P,h \<turnstile> v :\<le> T" by(blast dest: vs_confD addr_loc_type_fun)+
    with hext wt have "P,h' \<turnstile> ad'@al : T" "P,h' \<turnstile> v :\<le> T"
      by(blast intro: addr_loc_type_hext_mono conf_hext)+
    thus ?thesis using vs' obs
      by(auto simp add: take_Cons' intro!: vs_confI split: if_split_asm dest: vs_confD)
  next
    case False thus ?thesis using vs' by simp
  qed
qed

lemma heap_copies_non_speculative_typeable:
  assumes "heap_copies ad ad' als h obs h'"
  and "non_speculative P vs (llist_of (map NormalAction obs))"
  and "vs_conf P h vs"
  and "hconf h"
  and "list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) als Ts" "list_all2 (\<lambda>al T. P,h \<turnstile> ad'@al : T) als Ts"
  shows "heap_base.heap_copies (heap_read_typed P) heap_write ad ad' als h obs h'"
using assms
proof(induct arbitrary: Ts vs)
  case Nil show ?case by(auto intro: heap_base.heap_copies.intros)
next
  case (Cons al h ob h' als obs h'')
  note sc = \<open>non_speculative P vs (llist_of (map NormalAction (ob @ obs)))\<close>
    and vs = \<open>vs_conf P h vs\<close>
    and hconf = \<open>hconf h\<close>
    and wt = \<open>list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) (al # als) Ts\<close> \<open>list_all2 (\<lambda>al T. P,h \<turnstile> ad'@al : T) (al # als) Ts\<close>
  
  have sc1: "non_speculative P vs (llist_of (map NormalAction ob))" 
    and sc2: "non_speculative P (w_values P vs (map NormalAction ob)) (llist_of (map NormalAction obs))"
    using sc by(simp_all add: non_speculative_lappend lappend_llist_of_llist_of[symmetric] del: lappend_llist_of_llist_of)
  from wt obtain T Ts' where Ts: "Ts = T # Ts'" 
    and wt1: "P,h \<turnstile> ad@al : T" "P,h \<turnstile> ad'@al : T"
    and wt2: "list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) als Ts'" "list_all2 (\<lambda>al T. P,h \<turnstile> ad'@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)
  from \<open>heap_copy_loc ad ad' al h ob h'\<close> sc1 vs hconf wt1
  have copy: "heap_base.heap_copy_loc (heap_read_typed P) heap_write ad ad' al h ob h'"
    by(rule heap_copy_loc_non_speculative_typeable)+
  from heap_copy_loc_non_speculative_vs_conf[OF \<open>heap_copy_loc ad ad' al h ob h'\<close> _ vs hconf wt1, of "length ob"] sc1
  have vs': "vs_conf P h' (w_values P vs (map NormalAction ob))" by simp

  from \<open>heap_copy_loc ad ad' al h ob h'\<close>
  have "h \<unlhd> h'" by(rule hext_heap_copy_loc)
  with wt2 have wt2': "list_all2 (\<lambda>al T. P,h' \<turnstile> ad@al : T) als Ts'" "list_all2 (\<lambda>al T. P,h' \<turnstile> ad'@al : T) als Ts'"
    by -(erule List.list_all2_mono[OF _ addr_loc_type_hext_mono], assumption+)+

  from copy hconf wt1 have hconf': "hconf h'"
    by(rule heap_conf_read.hconf_heap_copy_loc_mono[OF heap_conf_read_heap_read_typed])
  
  from sc2 vs' hconf' wt2' have "heap_base.heap_copies (heap_read_typed P) heap_write ad ad' als h' obs h''" by(rule Cons)
  with copy show ?case by(rule heap_base.heap_copies.Cons)
qed

lemma heap_copies_non_speculative_vs_conf:
  assumes "heap_copies ad ad' als h obs h'"
  and "non_speculative P vs (llist_of (take n (map NormalAction obs)))"
  and "vs_conf P h vs"
  and "hconf h"
  and "list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) als Ts" "list_all2 (\<lambda>al T. P,h \<turnstile> ad'@al : T) als Ts"
  shows "vs_conf P h' (w_values P vs (take n (map NormalAction obs)))"
using assms
proof(induction arbitrary: Ts vs n)
  case Nil thus ?case by simp
next
  case (Cons al h ob h' als obs h'')
  note sc = \<open>non_speculative P vs (llist_of (take n (map NormalAction (ob @ obs))))\<close>
    and hcl = \<open>heap_copy_loc ad ad' al h ob h'\<close>
    and vs = \<open>vs_conf P h vs\<close>
    and hconf = \<open>hconf h\<close>
    and wt = \<open>list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) (al # als) Ts\<close> \<open>list_all2 (\<lambda>al T. P,h \<turnstile> ad'@al : T) (al # als) Ts\<close>
  let ?vs' = "w_values P vs (take n (map NormalAction ob))"

  from sc have sc1: "non_speculative P vs (llist_of (take n (map NormalAction ob)))"
    and sc2: "non_speculative P ?vs' (llist_of (take (n - length ob) (map NormalAction obs)))"
    by(simp_all add: lappend_llist_of_llist_of[symmetric] non_speculative_lappend del: lappend_llist_of_llist_of)
  
  from wt obtain T Ts' where Ts: "Ts = T # Ts'" 
    and wt1: "P,h \<turnstile> ad@al : T" "P,h \<turnstile> ad'@al : T"
    and wt2: "list_all2 (\<lambda>al T. P,h \<turnstile> ad@al : T) als Ts'" "list_all2 (\<lambda>al T. P,h \<turnstile> ad'@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)

  from hcl sc1 vs hconf wt1 have vs': "vs_conf P h' ?vs'" by(rule heap_copy_loc_non_speculative_vs_conf)

  show ?case
  proof(cases "n < length ob")
    case True
    from \<open>heap_copies ad ad' als h' obs h''\<close> have "h' \<unlhd> h''" by(rule hext_heap_copies)
    with vs' have "vs_conf P h'' ?vs'" by(rule vs_conf_hext)
    thus ?thesis using True by simp
  next
    case False
    note sc2 vs'
    moreover from False sc1 have sc1': "non_speculative P vs (llist_of (map NormalAction ob))" by simp
    with hcl have "heap_base.heap_copy_loc (heap_read_typed P) heap_write ad ad' al h ob h'"
      using vs hconf wt1 by(rule heap_copy_loc_non_speculative_typeable)
    hence "hconf h'" using hconf wt1
      by(rule heap_conf_read.hconf_heap_copy_loc_mono[OF heap_conf_read_heap_read_typed])
    moreover
    from hcl have "h \<unlhd> h'" by(rule hext_heap_copy_loc)
    with wt2 have wt2': "list_all2 (\<lambda>al T. P,h' \<turnstile> ad@al : T) als Ts'" "list_all2 (\<lambda>al T. P,h' \<turnstile> ad'@al : T) als Ts'"
      by -(erule List.list_all2_mono[OF _ addr_loc_type_hext_mono], assumption+)+
    ultimately have "vs_conf P h'' (w_values P ?vs' (take (n - length ob) (map NormalAction obs)))"
      by(rule Cons.IH)
    with False show ?thesis by simp
  qed
qed

lemma heap_clone_non_speculative_typeable_Some:
  assumes clone: "heap_clone P h ad h' \<lfloor>(obs, ad')\<rfloor>"
  and sc: "non_speculative P vs (llist_of (map NormalAction obs))"
  and vs: "vs_conf P h vs"
  and hconf: "hconf h"
  shows "heap_base.heap_clone allocate typeof_addr (heap_read_typed P) heap_write P h ad h' \<lfloor>(obs, ad')\<rfloor>"
using clone
proof(cases)
  case (ObjClone C h'' FDTs obs')
  note FDTs = \<open>P \<turnstile> C has_fields FDTs\<close>
    and obs = \<open>obs = NewHeapElem ad' (Class_type C) # obs'\<close>
  let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs"
  let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs"
  let ?vs = "w_value P vs (NormalAction (NewHeapElem ad' (Class_type C) :: ('addr, 'thread_id) obs_event))"
  from \<open>(h'', ad') \<in> allocate h (Class_type C)\<close> have hext: "h \<unlhd> h''" by(rule hext_heap_ops)
  hence type: "typeof_addr h'' ad = \<lfloor>Class_type C\<rfloor>" using \<open>typeof_addr h ad = \<lfloor>Class_type C\<rfloor>\<close> 
    by(rule typeof_addr_hext_mono)
    
  note \<open>heap_copies ad ad' ?als h'' obs' h'\<close>
  moreover from sc have "non_speculative P ?vs (llist_of (map NormalAction obs'))"
    by(simp add: obs)
  moreover from \<open>P \<turnstile> C has_fields FDTs\<close>
  have "is_class P C" by(rule has_fields_is_class)
  hence "is_htype P (Class_type C)" by simp
  with vs \<open>(h'', ad') \<in> allocate h (Class_type C)\<close>
  have "vs_conf P h'' ?vs" by(rule vs_conf_allocate)
  moreover from \<open>(h'', ad') \<in> allocate h (Class_type C)\<close> hconf \<open>is_htype P (Class_type C)\<close>
  have "hconf h''" by(rule hconf_allocate_mono)
  moreover from type FDTs have "list_all2 (\<lambda>al T. P,h'' \<turnstile> ad@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastforce intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
  moreover from \<open>(h'', ad') \<in> allocate h (Class_type C)\<close> \<open>is_htype P (Class_type C)\<close>
  have "typeof_addr h'' ad' = \<lfloor>Class_type C\<rfloor>" by(auto dest: allocate_SomeD)
  with FDTs have "list_all2 (\<lambda>al T. P,h'' \<turnstile> ad'@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastforce intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
  ultimately
  have copy: "heap_base.heap_copies (heap_read_typed P) heap_write ad ad' (map (\<lambda>((F, D), Tfm). CField D F) FDTs) h'' obs' h'"
    by(rule heap_copies_non_speculative_typeable)+
  from \<open>typeof_addr h ad = \<lfloor>Class_type C\<rfloor>\<close> \<open>(h'', ad') \<in> allocate h (Class_type C)\<close> FDTs copy
  show ?thesis unfolding obs by(rule heap_base.heap_clone.intros)
next
  case (ArrClone T n h'' FDTs obs')
  note obs = \<open>obs = NewHeapElem ad' (Array_type T n) # obs'\<close>
    and new = \<open>(h'', ad') \<in> allocate h (Array_type T n)\<close>
    and FDTs = \<open>P \<turnstile> Object has_fields FDTs\<close>
  let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<n]"
  let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs @ replicate n T"
  let ?vs = "w_value P vs (NormalAction (NewHeapElem ad' (Array_type T n) :: ('addr, 'thread_id) obs_event))"
  from new have hext: "h \<unlhd> h''" by(rule hext_heap_ops)
  hence type: "typeof_addr h'' ad = \<lfloor>Array_type T n\<rfloor>" using \<open>typeof_addr h ad = \<lfloor>Array_type T n\<rfloor>\<close> 
    by(rule typeof_addr_hext_mono)
  
  note \<open>heap_copies ad ad' ?als h'' obs' h'\<close>
  moreover from sc have "non_speculative P ?vs (llist_of (map NormalAction obs'))" by(simp add: obs)
  moreover from \<open>typeof_addr h ad = \<lfloor>Array_type T n\<rfloor>\<close> \<open>hconf h\<close> have "is_htype P (Array_type T n)"
    by(auto dest: typeof_addr_is_type)
  with vs new have "vs_conf P h'' ?vs" by(rule vs_conf_allocate)
  moreover from new hconf \<open>is_htype P (Array_type T n)\<close> have "hconf h''" by(rule hconf_allocate_mono)
  moreover
  from type FDTs have "list_all2 (\<lambda>al T. P,h'' \<turnstile> ad@al : T) ?als ?Ts"
    by(fastforce intro: list_all2_all_nthI addr_loc_type.intros simp add: has_field_def list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv dest: weak_map_of_SomeI)
  moreover from new \<open>is_htype P (Array_type T n)\<close>
  have "typeof_addr h'' ad' = \<lfloor>Array_type T n\<rfloor>"
    by(auto dest: allocate_SomeD)
  hence "list_all2 (\<lambda>al T. P,h'' \<turnstile> ad'@al : T) ?als ?Ts" using FDTs
    by(fastforce intro: list_all2_all_nthI addr_loc_type.intros simp add: has_field_def list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv dest: weak_map_of_SomeI)
  ultimately have copy: "heap_base.heap_copies (heap_read_typed P) heap_write ad ad' (map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<n]) h'' obs' h'"
    by(rule heap_copies_non_speculative_typeable)+
  from \<open>typeof_addr h ad = \<lfloor>Array_type T n\<rfloor>\<close> new FDTs copy show ?thesis
    unfolding obs by(rule heap_base.heap_clone.ArrClone)
qed

lemma heap_clone_non_speculative_vs_conf_Some:
  assumes clone: "heap_clone P h ad h' \<lfloor>(obs, ad')\<rfloor>"
  and sc: "non_speculative P vs (llist_of (take n (map NormalAction obs)))"
  and vs: "vs_conf P h vs"
  and hconf: "hconf h"
  shows "vs_conf P h' (w_values P vs (take n (map NormalAction obs)))"
using clone
proof(cases)
  case (ObjClone C h'' FDTs obs')
  note FDTs = \<open>P \<turnstile> C has_fields FDTs\<close>
    and obs = \<open>obs = NewHeapElem ad' (Class_type C) # obs'\<close>
  let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs"
  let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs"
  let ?vs = "w_value P vs (NormalAction (NewHeapElem ad' (Class_type C) :: ('addr, 'thread_id) obs_event))"
  from \<open>(h'', ad') \<in> allocate h (Class_type C)\<close> have hext: "h \<unlhd> h''" by(rule hext_heap_ops)
  hence type: "typeof_addr h'' ad = \<lfloor>Class_type C\<rfloor>" using \<open>typeof_addr h ad = \<lfloor>Class_type C\<rfloor>\<close> 
    by(rule typeof_addr_hext_mono)
    
  note \<open>heap_copies ad ad' ?als h'' obs' h'\<close>
  moreover from sc have "non_speculative P ?vs (llist_of (take (n - 1) (map NormalAction obs')))"
    by(simp add: obs take_Cons' split: if_split_asm)
  moreover from \<open>P \<turnstile> C has_fields FDTs\<close>
  have "is_class P C" by(rule has_fields_is_class)
  hence "is_htype P (Class_type C)" by simp
  with vs \<open>(h'', ad') \<in> allocate h (Class_type C)\<close>
  have "vs_conf P h'' ?vs" by(rule vs_conf_allocate)
  moreover from \<open>(h'', ad') \<in> allocate h (Class_type C)\<close> hconf \<open>is_htype P (Class_type C)\<close>
  have "hconf h''" by(rule hconf_allocate_mono)
  moreover from type FDTs have "list_all2 (\<lambda>al T. P,h'' \<turnstile> ad@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastforce intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
  moreover from \<open>(h'', ad') \<in> allocate h (Class_type C)\<close> \<open>is_htype P (Class_type C)\<close>
  have "typeof_addr h'' ad' = \<lfloor>Class_type C\<rfloor>" by(auto dest: allocate_SomeD)
  with FDTs have "list_all2 (\<lambda>al T. P,h'' \<turnstile> ad'@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastforce intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
  ultimately
  have vs': "vs_conf P h' (w_values P ?vs (take (n - 1) (map NormalAction obs')))"
    by(rule heap_copies_non_speculative_vs_conf)
  show ?thesis
  proof(cases "n > 0")
    case True
    with obs vs' show ?thesis by(simp add: take_Cons')
  next
    case False
    from \<open>heap_copies ad ad' ?als h'' obs' h'\<close> have "h'' \<unlhd> h'" by(rule hext_heap_copies)
    with \<open>h \<unlhd> h''\<close> have "h \<unlhd> h'" by(rule hext_trans)
    with vs have "vs_conf P h' vs" by(rule vs_conf_hext)
    thus ?thesis using False by simp
  qed
next
  case (ArrClone T N h'' FDTs obs')
  note obs = \<open>obs = NewHeapElem ad' (Array_type T N) # obs'\<close>
    and new = \<open>(h'', ad') \<in> allocate h (Array_type T N)\<close>
    and FDTs = \<open>P \<turnstile> Object has_fields FDTs\<close>
  let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<N]"
  let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs @ replicate N T"
  let ?vs = "w_value P vs (NormalAction (NewHeapElem ad' (Array_type T N) :: ('addr, 'thread_id) obs_event))"
  from new have hext: "h \<unlhd> h''" by(rule hext_heap_ops)
  hence type: "typeof_addr h'' ad = \<lfloor>Array_type T N\<rfloor>" using \<open>typeof_addr h ad = \<lfloor>Array_type T N\<rfloor>\<close> 
    by(rule typeof_addr_hext_mono)
  
  note \<open>heap_copies ad ad' ?als h'' obs' h'\<close>
  moreover from sc have "non_speculative P ?vs (llist_of (take (n - 1) (map NormalAction obs')))"
    by(simp add: obs take_Cons' split: if_split_asm)
  moreover from \<open>typeof_addr h ad = \<lfloor>Array_type T N\<rfloor>\<close> \<open>hconf h\<close> have "is_htype P (Array_type T N)"
    by(auto dest: typeof_addr_is_type)
  with vs new have "vs_conf P h'' ?vs" by(rule vs_conf_allocate)
  moreover from new hconf \<open>is_htype P (Array_type T N)\<close> have "hconf h''" by(rule hconf_allocate_mono)
  moreover
  from type FDTs have "list_all2 (\<lambda>al T. P,h'' \<turnstile> ad@al : T) ?als ?Ts"
    by(fastforce intro: list_all2_all_nthI addr_loc_type.intros simp add: has_field_def list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv dest: weak_map_of_SomeI)
  moreover from new \<open>is_htype P (Array_type T N)\<close>
  have "typeof_addr h'' ad' = \<lfloor>Array_type T N\<rfloor>"
    by(auto dest: allocate_SomeD)
  hence "list_all2 (\<lambda>al T. P,h'' \<turnstile> ad'@al : T) ?als ?Ts" using FDTs
    by(fastforce intro: list_all2_all_nthI addr_loc_type.intros simp add: has_field_def list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv dest: weak_map_of_SomeI)
  ultimately have vs': "vs_conf P h' (w_values P ?vs (take (n - 1) (map NormalAction obs')))"
    by(rule heap_copies_non_speculative_vs_conf)
  show ?thesis
  proof(cases "n > 0")
    case True
    with obs vs' show ?thesis by(simp add: take_Cons')
  next
    case False
    from \<open>heap_copies ad ad' ?als h'' obs' h'\<close> have "h'' \<unlhd> h'" by(rule hext_heap_copies)
    with \<open>h \<unlhd> h''\<close> have "h \<unlhd> h'" by(rule hext_trans)
    with vs have "vs_conf P h' vs" by(rule vs_conf_hext)
    thus ?thesis using False by simp
  qed
qed

lemma heap_clone_non_speculative_typeable_None:
  assumes "heap_clone P h ad h' None"
  shows "heap_base.heap_clone allocate typeof_addr (heap_read_typed P) heap_write P h ad h' None"
using assms
by(cases)(blast intro: heap_base.heap_clone.intros)+

lemma red_external_non_speculative_typeable:
  assumes red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and sc: "non_speculative P Vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
  and vs: "vs_conf P h Vs"
  and hconf: "hconf h"
  shows "heap_base.red_external addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_read_typed P) heap_write P t h a M vs ta va h'"
using assms
by(cases)(auto intro: heap_base.red_external.intros heap_clone_non_speculative_typeable_None heap_clone_non_speculative_typeable_Some dest: hext_heap_clone elim: vs_conf_hext)

lemma red_external_non_speculative_vs_conf:
  assumes red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and sc: "non_speculative P Vs (llist_of (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
  and vs: "vs_conf P h Vs"
  and hconf: "hconf h"
  shows "vs_conf P h' (w_values P Vs (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
using assms
by(cases)(auto intro: heap_base.red_external.intros heap_clone_non_speculative_vs_conf_Some dest: hext_heap_clone elim: vs_conf_hext simp add: take_Cons')

lemma red_external_aggr_non_speculative_typeable:
  assumes red: "(ta, va, h') \<in> red_external_aggr P t a M vs h"
  and sc: "non_speculative P Vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
  and vs: "vs_conf P h Vs"
  and hconf: "hconf h"
  and native: "is_native P (the (typeof_addr h a)) M"
  shows "(ta, va, h') \<in> heap_base.red_external_aggr addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_read_typed P) heap_write P t a M vs h"
using assms
by(cases "the (typeof_addr h a)")(auto 4 3 simp add: is_native.simps external_WT_defs.simps red_external_aggr_def heap_base.red_external_aggr_def split: if_split_asm split del: if_split del: disjCI intro: heap_clone_non_speculative_typeable_None heap_clone_non_speculative_typeable_Some dest: sees_method_decl_above)

lemma red_external_aggr_non_speculative_vs_conf:
  assumes red: "(ta, va, h') \<in> red_external_aggr P t a M vs h"
  and sc: "non_speculative P Vs (llist_of (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
  and vs: "vs_conf P h Vs"
  and hconf: "hconf h"
  and native: "is_native P (the (typeof_addr h a)) M"
  shows "vs_conf P h' (w_values P Vs (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
using assms
by(cases "the (typeof_addr h a)")(auto 4 3 simp add: is_native.simps external_WT_defs.simps red_external_aggr_def heap_base.red_external_aggr_def take_Cons' split: if_split_asm split del: if_split del: disjCI intro: heap_clone_non_speculative_vs_conf_Some dest: hext_heap_clone elim: vs_conf_hext dest: sees_method_decl_above)

end

declare split_paired_Ex [simp del]
declare eq_upto_seq_inconsist_simps [simp]

context heap_progress begin

lemma heap_copy_loc_non_speculative_read:
  assumes hrt: "heap_read_typeable hconf P"
  and vs: "vs_conf P h vs"
  and type: "P,h \<turnstile> a@al : T" "P,h \<turnstile> a'@al : T"
  and hconf: "hconf h"
  and copy: "heap_copy_loc a a' al h obs h'"
  and i: "i < length obs"
  and read: "obs ! i = ReadMem a'' al'' v"
  and v: "v' \<in> w_values P vs (map NormalAction (take i obs)) (a'', al'')"
  shows "\<exists>obs' h''. heap_copy_loc a a' al h obs' h'' \<and> i < length obs' \<and> take i obs' = take i obs \<and> 
                    obs' ! i = ReadMem a'' al'' v' \<and> length obs' \<le> length obs \<and> 
                    non_speculative P vs (llist_of (map NormalAction obs'))"
using copy
proof cases
  case (1 v'')
  with read i have [simp]: "i = 0" "v'' = v" "a'' = a" "al'' = al"
    by(simp_all add: nth_Cons split: nat.split_asm)
  from v have "v' \<in> vs (a, al)" by simp
  with vs type have conf: "P,h \<turnstile> v' :\<le> T" by(auto dest: addr_loc_type_fun vs_confD)
  let ?obs'' = "[ReadMem a al v', WriteMem a' al v']"
  from hrt type(1) conf hconf have "heap_read h a al v'" by(rule heap_read_typeableD)
  moreover from heap_write_total[OF hconf type(2) conf] 
  obtain h'' where "heap_write h a' al v' h''" ..
  ultimately have "heap_copy_loc a a' al h ?obs'' h''" ..
  thus ?thesis using 1 \<open>v' \<in> vs (a, al)\<close> by(auto)
qed

lemma heap_copies_non_speculative_read:
  assumes hrt: "heap_read_typeable hconf P"
  and copies: "heap_copies a a' als h obs h'"
  and vs: "vs_conf P h vs"
  and type1: "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts"
  and type2: "list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) als Ts"
  and hconf: "hconf h"
  and i: "i < length obs"
  and read: "obs ! i = ReadMem a'' al'' v"
  and v: "v' \<in> w_values P vs (map NormalAction (take i obs)) (a'', al'')"
  and ns: "non_speculative P vs (llist_of (map NormalAction (take i obs)))"
  shows "\<exists>obs' h''. heap_copies a a' als h obs' h'' \<and> i < length obs' \<and> take i obs' = take i obs \<and> 
                    obs' ! i = ReadMem a'' al'' v' \<and> length obs' \<le> length obs"
  (is "?concl als h obs vs i")
using copies vs type1 type2 hconf i read v ns
proof(induction arbitrary: Ts vs i)
  case Nil thus ?case by simp
next
  case (Cons al h ob h' als obs h'' Ts vs)
  note copy = \<open>heap_copy_loc a a' al h ob h'\<close>
  note vs = \<open>vs_conf P h vs\<close>
  note type1 = \<open>list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) (al # als) Ts\<close>
    and type2 = \<open>list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) (al # als) Ts\<close>
  note hconf = \<open>hconf h\<close>
  note i = \<open>i < length (ob @ obs)\<close>
  note read = \<open>(ob @ obs) ! i = ReadMem a'' al'' v\<close>
  note v = \<open>v' \<in> w_values P vs (map NormalAction (take i (ob @ obs))) (a'', al'')\<close>
  note ns = \<open>non_speculative P vs (llist_of (map NormalAction (take i (ob @ obs))))\<close>

  from type1 obtain T Ts' where Ts: "Ts = T # Ts'"
    and type1': "P,h \<turnstile> a@al : T"
    and type1'': "list_all2 (\<lambda>al T. P,h \<turnstile> a@al : T) als Ts'"
    by(auto simp add: list_all2_Cons1)
  from type2 Ts have type2': "P,h \<turnstile> a'@al : T"
    and type2'': "list_all2 (\<lambda>al T. P,h \<turnstile> a'@al : T) als Ts'"
    by simp_all
  show ?case
  proof(cases "i < length ob")
    case True
    with read v
    have "ob ! i = ReadMem a'' al'' v"
      and "v' \<in> w_values P vs (map NormalAction (take i ob)) (a'', al'')" by(simp_all add: nth_append)
    from heap_copy_loc_non_speculative_read[OF hrt vs type1' type2' hconf copy True this]
    obtain ob' H'' where copy': "heap_copy_loc a a' al h ob' H''"
      and i': "i < length ob'" and "take i ob' = take i ob"
      and "ob' ! i = ReadMem a'' al'' v'"
      and "length ob' \<le> length ob"
      and ns: "non_speculative P vs (llist_of (map NormalAction ob'))" by blast
    moreover {
      from copy' have hext: "h \<unlhd> H''" by(rule hext_heap_copy_loc)
      have "hconf H''" 
        by(rule heap_conf_read.hconf_heap_copy_loc_mono[OF heap_conf_read_heap_read_typed])(rule heap_copy_loc_non_speculative_typeable[OF copy' ns vs hconf type1' type2'], fact+)
      moreover
      from type1'' have "list_all2 (\<lambda>al T. P,H'' \<turnstile> a@al : T) als Ts'"
        by(rule List.list_all2_mono)(rule addr_loc_type_hext_mono[OF _ hext])
      moreover from type2'' have "list_all2 (\<lambda>al T. P,H'' \<turnstile> a'@al : T) als Ts'"
        by(rule List.list_all2_mono)(rule addr_loc_type_hext_mono[OF _ hext])
      moreover note calculation }
    from heap_copies_progress[OF this]
    obtain obs' h''' where *: "heap_copies a a' als H'' obs' h'''" by blast
    moreover note heap_copies_length[OF *]
    moreover note heap_copy_loc_length[OF copy']
    moreover note heap_copies_length[OF \<open>heap_copies a a' als h' obs h''\<close>]
    ultimately show ?thesis using True by(auto intro!: heap_copies.Cons exI simp add: nth_append)
  next
    case False
    let ?vs' = "w_values P vs (map NormalAction ob)"
    let ?i' = "i - length ob"

    from ns False obtain ns': "non_speculative P vs (llist_of (map NormalAction ob))"
      and ns'': "non_speculative P ?vs' (llist_of (map NormalAction (take ?i' obs)))"
      by(simp add: lappend_llist_of_llist_of[symmetric] non_speculative_lappend del: lappend_llist_of_llist_of)

    from heap_copy_loc_non_speculative_vs_conf[OF copy _ vs hconf type1' type2', where n="length ob"] ns'
    have "vs_conf P h' ?vs'" by simp
    moreover
    from copy have hext: "h \<unlhd> h'" by(rule hext_heap_copy_loc)
    from type1'' have "list_all2 (\<lambda>al T. P,h' \<turnstile> a@al : T) als Ts'"
      by(rule List.list_all2_mono)(rule addr_loc_type_hext_mono[OF _ hext])
    moreover from type2'' have "list_all2 (\<lambda>al T. P,h' \<turnstile> a'@al : T) als Ts'"
      by(rule List.list_all2_mono)(rule addr_loc_type_hext_mono[OF _ hext])
    moreover have "hconf h'" 
      by(rule heap_conf_read.hconf_heap_copy_loc_mono[OF heap_conf_read_heap_read_typed])(rule heap_copy_loc_non_speculative_typeable[OF copy ns' vs hconf type1' type2'], fact+)
    moreover from i False have "?i' < length obs" by simp
    moreover from read False have "obs ! ?i' = ReadMem a'' al'' v" by(simp add: nth_append)
    moreover from v False have "v' \<in> w_values P ?vs' (map NormalAction (take ?i' obs)) (a'', al'')" by(simp)
    ultimately have "?concl als h' obs ?vs' ?i'" using ns'' by(rule Cons.IH)
    thus ?thesis using False copy by safe(auto intro!: heap_copies.Cons exI simp add: nth_append)
  qed
qed

lemma heap_clone_non_speculative_read:
  assumes hrt: "heap_read_typeable hconf P"
  and clone: "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and vs: "vs_conf P h vs"
  and hconf: "hconf h"
  and i: "i < length obs"
  and read: "obs ! i = ReadMem a'' al'' v"
  and v: "v' \<in> w_values P vs (map NormalAction (take i obs)) (a'', al'')"
  and ns: "non_speculative P vs (llist_of (map NormalAction (take i obs)))"
  shows "\<exists>obs' h''. heap_clone P h a h'' \<lfloor>(obs', a')\<rfloor> \<and> i < length obs' \<and> take i obs' = take i obs \<and> 
                    obs' ! i = ReadMem a'' al'' v' \<and> length obs' \<le> length obs"
using clone
proof cases
  case (ObjClone C h'' FDTs obs')

  note obs = \<open>obs = NewHeapElem a' (Class_type C) # obs'\<close>
  note FDTs = \<open>P \<turnstile> C has_fields FDTs\<close>
  let ?als = "map (\<lambda>((F, D), Tm). CField D F) FDTs"
  let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs"
  let ?vs = "w_value P vs (NormalAction (NewHeapElem a' (Class_type C)) :: ('addr, 'thread_id) obs_event action)"
  let ?i = "i - 1"
  from i read obs have i_0: "i > 0" by(simp add: nth_Cons' split: if_split_asm)

  from \<open>P \<turnstile> C has_fields FDTs\<close> have "is_class P C" by(rule has_fields_is_class)
  with \<open>(h'', a') \<in> allocate h (Class_type C)\<close>
  have type_a': "typeof_addr h'' a' = \<lfloor>Class_type C\<rfloor>" and hext: "h \<unlhd> h''"
    by(auto dest: allocate_SomeD hext_allocate)

  note \<open>heap_copies a a' ?als h'' obs' h'\<close>
  moreover from \<open>typeof_addr h a = \<lfloor>Class_type C\<rfloor>\<close> hconf have "is_htype P (Class_type C)"
    by(rule typeof_addr_is_type)
  with vs \<open>(h'', a') \<in> allocate h (Class_type C)\<close>
  have "vs_conf P h'' ?vs" by(rule vs_conf_allocate)
  moreover
  from hext \<open>typeof_addr h a = \<lfloor>Class_type C\<rfloor>\<close>
  have "typeof_addr h'' a = \<lfloor>Class_type C\<rfloor>" by(rule typeof_addr_hext_mono)
  hence "list_all2 (\<lambda>al T. P,h'' \<turnstile> a@al : T) ?als ?Ts" using FDTs
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastforce intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
  moreover from FDTs type_a'
  have "list_all2 (\<lambda>al T. P,h'' \<turnstile> a'@al : T) ?als ?Ts"
    unfolding list_all2_map1 list_all2_map2 list_all2_refl_conv
    by(fastforce intro: addr_loc_type.intros simp add: has_field_def dest: weak_map_of_SomeI)
  moreover from \<open>(h'', a') \<in> allocate h (Class_type C)\<close> hconf \<open>is_htype P (Class_type C)\<close>
  have "hconf h''" by(rule hconf_allocate_mono)
  moreover from i read i_0 obs have "?i < length obs'" "obs' ! ?i = ReadMem a'' al'' v" by simp_all
  moreover from v i_0 obs
  have "v' \<in> w_values P ?vs (map NormalAction (take ?i obs')) (a'', al'')" by(simp add: take_Cons')
  moreover from ns i_0 obs
  have "non_speculative P ?vs (llist_of (map NormalAction (take ?i obs')))" by(simp add: take_Cons')
  ultimately have "\<exists>obs'' h'''. heap_copies a a' ?als h'' obs'' h''' \<and>
                             ?i < length obs'' \<and> take ?i obs'' = take ?i obs' \<and> obs'' ! ?i = ReadMem a'' al'' v' \<and>
                             length obs'' \<le> length obs'"
    by(rule heap_copies_non_speculative_read[OF hrt])
  thus ?thesis using \<open>typeof_addr h a = \<lfloor>Class_type C\<rfloor>\<close> \<open>(h'', a') \<in> allocate h (Class_type C)\<close> FDTs obs i_0
    by(auto 4 4 intro: heap_clone.ObjClone simp add: take_Cons')
next
  case (ArrClone T n h'' FDTs obs')

  note obs = \<open>obs = NewHeapElem a' (Array_type T n) # obs'\<close>
  note FDTs = \<open>P \<turnstile> Object has_fields FDTs\<close>
  let ?als = "map (\<lambda>((F, D), Tfm). CField D F) FDTs @ map ACell [0..<n]"
  let ?Ts = "map (\<lambda>(FD, T). fst (the (map_of FDTs FD))) FDTs @ replicate n T"
  let ?vs = "w_value P vs (NormalAction (NewHeapElem a' (Array_type T n)) :: ('addr, 'thread_id) obs_event action)"
  let ?i = "i - 1"
  from i read obs have i_0: "i > 0" by(simp add: nth_Cons' split: if_split_asm)

  from \<open>typeof_addr h a = \<lfloor>Array_type T n\<rfloor>\<close> hconf
  have "is_htype P (Array_type T n)" by(rule typeof_addr_is_type)
  with \<open>(h'', a') \<in> allocate h (Array_type T n)\<close>
  have type_a': "typeof_addr h'' a' = \<lfloor>Array_type T n\<rfloor>"
    and hext: "h \<unlhd> h''"
    by(auto dest: allocate_SomeD hext_allocate)

  note \<open>heap_copies a a' ?als h'' obs' h'\<close>
  moreover from vs \<open>(h'', a') \<in> allocate h (Array_type T n)\<close> \<open>is_htype P (Array_type T n)\<close>
  have "vs_conf P h'' ?vs" by(rule vs_conf_allocate)
  moreover from hext \<open>typeof_addr h a = \<lfloor>Array_type T n\<rfloor>\<close>
  have type'a: "typeof_addr h'' a = \<lfloor>Array_type T n\<rfloor>"
    by(auto intro: hext_arrD)
  from type'a FDTs have "list_all2 (\<lambda>al T. P,h'' \<turnstile> a@al : T) ?als ?Ts"
    by(fastforce intro: list_all2_all_nthI addr_loc_type.intros simp add: has_field_def list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv dest: weak_map_of_SomeI)
  moreover from type_a' FDTs
  have "list_all2 (\<lambda>al T. P,h'' \<turnstile> a'@al : T) ?als ?Ts"
    by(fastforce intro: list_all2_all_nthI addr_loc_type.intros simp add: has_field_def list_all2_append list_all2_map1 list_all2_map2 list_all2_refl_conv dest: weak_map_of_SomeI)
  moreover from \<open>(h'', a') \<in> allocate h (Array_type T n)\<close> hconf \<open>is_htype P (Array_type T n)\<close>
  have "hconf h''" by(rule hconf_allocate_mono)
  moreover from i read i_0 obs have "?i < length obs'" "obs' ! ?i = ReadMem a'' al'' v" by simp_all
  moreover from v i_0 obs
  have "v' \<in> w_values P ?vs (map NormalAction (take ?i obs')) (a'', al'')" by(simp add: take_Cons')
  moreover from ns i_0 obs
  have "non_speculative P ?vs (llist_of (map NormalAction (take ?i obs')))" by(simp add: take_Cons')
  ultimately have "\<exists>obs'' h'''. heap_copies a a' ?als h'' obs'' h''' \<and>
                             ?i < length obs'' \<and> take ?i obs'' = take ?i obs' \<and> obs'' ! ?i = ReadMem a'' al'' v' \<and>
                             length obs'' \<le> length obs'"
    by(rule heap_copies_non_speculative_read[OF hrt])
  thus ?thesis using \<open>typeof_addr h a = \<lfloor>Array_type T n\<rfloor>\<close> \<open>(h'', a') \<in> allocate h (Array_type T n)\<close> FDTs obs i_0
    by(auto 4 4 intro: heap_clone.ArrClone simp add: take_Cons')
qed

lemma red_external_non_speculative_read:
  assumes hrt: "heap_read_typeable hconf P"
  and vs: "vs_conf P (shr s) vs"
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs'), shr s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>"
  and aok: "final_thread.actions_ok final s t ta"
  and hconf: "hconf (shr s)"
  and i: "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and read: "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = ReadMem a'' al'' v"
  and v: "v' \<in> w_values P vs (map NormalAction (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (a'', al'')"
  and ns: "non_speculative P vs (llist_of (map NormalAction (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
  shows "\<exists>ta'' va'' h''. P,t \<turnstile> \<langle>a\<bullet>M(vs'), shr s\<rangle> -ta''\<rightarrow>ext \<langle>va'', h''\<rangle> \<and> final_thread.actions_ok final s t ta'' \<and>
                         i < length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> \<and> take i \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> 
                         \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> ! i = ReadMem a'' al'' v' \<and> length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> \<le> length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using red i read
proof cases
  case [simp]: (RedClone obs a')
  from heap_clone_non_speculative_read[OF hrt \<open>heap_clone P (shr s) a h' \<lfloor>(obs, a')\<rfloor>\<close> vs hconf, of i a'' al'' v v'] i read v ns
  show ?thesis using aok
    by(fastforce intro: red_external.RedClone simp add: final_thread.actions_ok_iff)
qed(auto simp add: nth_Cons)

lemma red_external_aggr_non_speculative_read:
  assumes hrt: "heap_read_typeable hconf P"
  and vs: "vs_conf P (shr s) vs"
  and red: "(ta, va, h') \<in> red_external_aggr P t a M vs' (shr s)"
  and native: "is_native P (the (typeof_addr (shr s) a)) M"
  and aok: "final_thread.actions_ok final s t ta"
  and hconf: "hconf (shr s)"
  and i: "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and read: "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = ReadMem a'' al'' v"
  and v: "v' \<in> w_values P vs (map NormalAction (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (a'', al'')"
  and ns: "non_speculative P vs (llist_of (map NormalAction (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
  shows "\<exists>ta'' va'' h''. (ta'', va'', h'') \<in> red_external_aggr P t a M vs' (shr s) \<and> final_thread.actions_ok final s t ta'' \<and>
                         i < length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> \<and> take i \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> 
                         \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> ! i = ReadMem a'' al'' v' \<and> length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> \<le> length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using red native aok hconf i read v ns
apply(simp add: red_external_aggr_def final_thread.actions_ok_iff ex_disj_distrib conj_disj_distribR split nth_Cons' del: if_split split: if_split_asm disj_split_asm)
apply(drule heap_clone_non_speculative_read[OF hrt _ vs hconf, of _ _ _ _ i a'' al'' v v'])
apply simp_all
apply(fastforce)
done

end

declare split_paired_Ex [simp]
declare eq_upto_seq_inconsist_simps [simp del]


context allocated_heap begin

lemma heap_copy_loc_allocated_same:
  assumes "heap_copy_loc a a' al h obs h'"
  shows "allocated h' = allocated h"
using assms
by cases(auto del: subsetI simp: heap_write_allocated_same)

lemma heap_copy_loc_allocated_mono:
  "heap_copy_loc a a' al h obs h' \<Longrightarrow> allocated h \<subseteq> allocated h'"
by(simp add: heap_copy_loc_allocated_same)

lemma heap_copies_allocated_same:
  assumes "heap_copies a a' al h obs h'"
  shows "allocated h' = allocated h"
using assms
by(induct)(auto simp add: heap_copy_loc_allocated_same)

lemma heap_copies_allocated_mono:
  "heap_copies a a' al h obs h' \<Longrightarrow> allocated h \<subseteq> allocated h'"
by(simp add: heap_copies_allocated_same)

lemma heap_clone_allocated_mono:
  assumes "heap_clone P h a h' aobs"
  shows "allocated h \<subseteq> allocated h'"
using assms
by cases(blast del: subsetI intro: heap_copies_allocated_mono allocate_allocated_mono intro: subset_trans)+

lemma red_external_allocated_mono:
  assumes "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  shows "allocated h \<subseteq> allocated h'"
using assms
by(cases)(blast del: subsetI intro: heap_clone_allocated_mono heap_write_allocated_same)+

lemma red_external_aggr_allocated_mono:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; is_native P (the (typeof_addr h a)) M \<rbrakk>
  \<Longrightarrow> allocated h \<subseteq> allocated h'"
by(cases "the (typeof_addr h a)")(auto simp add: is_native.simps external_WT_defs.simps red_external_aggr_def split: if_split_asm dest: heap_clone_allocated_mono sees_method_decl_above)

lemma heap_clone_allocatedD:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "NewHeapElem a'' x \<in> set obs"
  shows "a'' \<in> allocated h' \<and> a'' \<notin> allocated h"
using assms
by cases(auto dest: allocate_allocatedD heap_copies_allocated_mono heap_copies_not_New)

lemma red_external_allocatedD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewHeapElem a' x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> a' \<in> allocated h' \<and> a' \<notin> allocated h"
by(erule red_external.cases)(auto dest: heap_clone_allocatedD)

lemma red_external_aggr_allocatedD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; NewHeapElem a' x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     is_native P (the (typeof_addr h a)) M \<rbrakk>
  \<Longrightarrow> a' \<in> allocated h' \<and> a' \<notin> allocated h"
by(auto simp add: is_native.simps external_WT_defs.simps red_external_aggr_def split: if_split_asm dest: heap_clone_allocatedD sees_method_decl_above)

lemma heap_clone_NewHeapElemD:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "ad \<in> allocated h'"
  and "ad \<notin> allocated h"
  shows "\<exists>CTn. NewHeapElem ad CTn \<in> set obs"
using assms
by cases(auto dest!: allocate_allocatedD heap_copies_allocated_same)

lemma heap_clone_fail_allocated_same:
  assumes "heap_clone P h a h' None"
  shows "allocated h' = allocated h"
using assms
by(cases)(auto)

lemma red_external_NewHeapElemD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; a' \<in> allocated h'; a' \<notin> allocated h \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a' CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
by(erule red_external.cases)(auto dest: heap_clone_NewHeapElemD heap_clone_fail_allocated_same)

lemma red_external_aggr_NewHeapElemD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; a' \<in> allocated h'; a' \<notin> allocated h;
     is_native P (the (typeof_addr h a)) M \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a' CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
by(cases "the (typeof_addr h a)")(auto simp add: is_native.simps external_WT_defs.simps red_external_aggr_def split: if_split_asm dest: heap_clone_fail_allocated_same heap_clone_NewHeapElemD sees_method_decl_above)

end

context heap_base begin

lemma binop_known_addrs:
  assumes ok: "start_heap_ok"
  shows "binop bop v1 v2 = \<lfloor>Inl v\<rfloor> \<Longrightarrow> ka_Val v \<subseteq> ka_Val v1 \<union> ka_Val v2 \<union> set start_addrs"
  and "binop bop v1 v2 = \<lfloor>Inr a\<rfloor> \<Longrightarrow> a \<in> ka_Val v1 \<union> ka_Val v2 \<union> set start_addrs"
apply(cases bop, auto split: if_split_asm)[1]
apply(cases bop, auto split: if_split_asm simp add: addr_of_sys_xcpt_start_addr[OF ok])
done

lemma heap_copy_loc_known_addrs_ReadMem:
  assumes "heap_copy_loc a a' al h ob h'"
  and "ReadMem ad al' v \<in> set ob"
  shows "ad = a"
using assms by cases simp

lemma heap_copies_known_addrs_ReadMem:
  assumes "heap_copies a a' als h obs h'"
  and "ReadMem ad al v \<in> set obs"
  shows "ad = a"
using assms
by(induct)(auto dest: heap_copy_loc_known_addrs_ReadMem)

lemma heap_clone_known_addrs_ReadMem:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "ReadMem ad al v \<in> set obs"
  shows "ad = a"
using assms
by cases(auto dest: heap_copies_known_addrs_ReadMem)

lemma red_external_known_addrs_ReadMem:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> {thread_id2addr t, a} \<union> (\<Union>(ka_Val ` set vs)) \<union> set start_addrs"
by(erule red_external.cases)(simp_all add: heap_clone_known_addrs_ReadMem)

lemma red_external_aggr_known_addrs_ReadMem:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> {thread_id2addr t, a} \<union> (\<Union>(ka_Val ` set vs)) \<union> set start_addrs"
apply(auto simp add: red_external_aggr_def split: if_split_asm dest: heap_clone_known_addrs_ReadMem)
done

lemma heap_copy_loc_known_addrs_WriteMem:
  assumes "heap_copy_loc a a' al h ob h'"
  and "ob ! n = WriteMem ad al' (Addr a'')" "n < length ob"
  shows "a'' \<in> new_obs_addrs (take n ob)"
using assms
by cases(auto simp add: nth_Cons new_obs_addrs_def split: nat.split_asm)

lemma heap_copies_known_addrs_WriteMem:
  assumes "heap_copies a a' als h obs h'"
  and "obs ! n = WriteMem ad al (Addr a'')" "n < length obs"
  shows "a'' \<in> new_obs_addrs (take n obs)"
using assms
by(induct arbitrary: n)(auto simp add: nth_append new_obs_addrs_def dest: heap_copy_loc_known_addrs_WriteMem split: if_split_asm)

lemma heap_clone_known_addrs_WriteMem:
  assumes "heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>"
  and "obs ! n = WriteMem ad al (Addr a'')" "n < length obs"
  shows "a'' \<in> new_obs_addrs (take n obs)"
using assms
by cases(auto simp add: nth_Cons new_obs_addrs_def split: nat.split_asm dest: heap_copies_known_addrs_WriteMem)

lemma red_external_known_addrs_WriteMem:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr a'); n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> a' \<in> {thread_id2addr t, a} \<union> (\<Union>(ka_Val ` set vs)) \<union> set start_addrs \<union> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
by(erule red_external.cases)(auto dest: heap_clone_known_addrs_WriteMem)

lemma red_external_aggr_known_addrs_WriteMem:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr a'); n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> a' \<in> {thread_id2addr t, a} \<union> (\<Union>(ka_Val ` set vs)) \<union> set start_addrs \<union> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
apply(auto simp add: red_external_aggr_def split: if_split_asm dest: heap_clone_known_addrs_WriteMem)
done

lemma red_external_known_addrs_mono:
  assumes ok: "start_heap_ok"
  and red: "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  shows "(case va of RetVal v \<Rightarrow> ka_Val v | RetExc a \<Rightarrow> {a} | RetStaySame \<Rightarrow> {}) \<subseteq> {thread_id2addr t, a} \<union> (\<Union>(ka_Val ` set vs)) \<union> set start_addrs \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using red
by cases(auto simp add: addr_of_sys_xcpt_start_addr[OF ok] new_obs_addrs_def heap_clone.simps)

lemma red_external_aggr_known_addrs_mono:
  assumes ok: "start_heap_ok"
  and red: "(ta, va, h') \<in> red_external_aggr P t a M vs h" "is_native P (the (typeof_addr h a)) M"
  shows "(case va of RetVal v \<Rightarrow> ka_Val v | RetExc a \<Rightarrow> {a} | RetStaySame \<Rightarrow> {}) \<subseteq> {thread_id2addr t, a} \<union> (\<Union>(ka_Val ` set vs)) \<union> set start_addrs \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using red
apply(cases "the (typeof_addr h a)")
apply(auto simp add: red_external_aggr_def addr_of_sys_xcpt_start_addr[OF ok] new_obs_addrs_def heap_clone.simps split: if_split_asm)
apply(auto simp add: is_native.simps elim!: external_WT_defs.cases dest: sees_method_decl_above)
done

lemma red_external_NewThread_idD:
  "\<lbrakk> P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>; NewThread t' (C, M', a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> t' = addr2thread_id a \<and> a' = a"
by(erule red_external.cases) simp_all

lemma red_external_aggr_NewThread_idD:
  "\<lbrakk> (ta, va, h') \<in> red_external_aggr P t a M vs h; 
     NewThread t' (C, M', a') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> t' = addr2thread_id a \<and> a' = a"
apply(auto simp add: red_external_aggr_def split: if_split_asm)
done

end

locale heap'' = 
  heap'
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and P :: "'m prog"
  +
  assumes allocate_typeof_addr_SomeD: "\<lbrakk> (h', a) \<in> allocate h hT; typeof_addr a \<noteq> None \<rbrakk> \<Longrightarrow> typeof_addr a = \<lfloor>hT\<rfloor>"
begin

lemma heap_copy_loc_New_type_match:
  "\<lbrakk> h.heap_copy_loc a a' al h obs h'; NewHeapElem ad CTn \<in> set obs; typeof_addr ad \<noteq> None \<rbrakk>
  \<Longrightarrow> typeof_addr ad = \<lfloor>CTn\<rfloor>"
by(erule h.heap_copy_loc.cases) simp

lemma heap_copies_New_type_match:
  "\<lbrakk> h.heap_copies a a' als h obs h'; NewHeapElem ad CTn \<in> set obs; typeof_addr ad \<noteq> None \<rbrakk>
  \<Longrightarrow> typeof_addr ad = \<lfloor>CTn\<rfloor>"
by(induct rule: h.heap_copies.induct)(auto dest: heap_copy_loc_New_type_match)

lemma heap_clone_New_type_match:
  "\<lbrakk> h.heap_clone P h a h' \<lfloor>(obs, a')\<rfloor>; NewHeapElem ad CTn \<in> set obs; typeof_addr ad \<noteq> None \<rbrakk>
  \<Longrightarrow> typeof_addr ad = \<lfloor>CTn\<rfloor>"
by(erule h.heap_clone.cases)(auto dest: allocate_typeof_addr_SomeD heap_copies_New_type_match)

lemma red_external_New_type_match:
  "\<lbrakk> h.red_external P t a M vs h ta va h'; NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; typeof_addr ad \<noteq> None \<rbrakk>
  \<Longrightarrow> typeof_addr ad = \<lfloor>CTn\<rfloor>"
by(erule h.red_external.cases)(auto dest: heap_clone_New_type_match)

lemma red_external_aggr_New_type_match:
  "\<lbrakk> (ta, va, h') \<in> h.red_external_aggr P t a M vs h; NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; typeof_addr ad \<noteq> None \<rbrakk>
  \<Longrightarrow> typeof_addr ad = \<lfloor>CTn\<rfloor>"
by(auto simp add: h.red_external_aggr_def split: if_split_asm dest: heap_clone_New_type_match)

end

end
