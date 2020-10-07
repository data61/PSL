(*  Title:      JinjaThreads/Common/StartConfig.thy
    Author:     Andreas Lochbihler
*)

section \<open>The initial configuration\<close>

theory StartConfig
imports
  Exceptions
  Observable_Events
begin

definition initialization_list :: "cname list"
where
  "initialization_list = Thread # sys_xcpts_list"

context heap_base begin

definition create_initial_object :: "'heap \<times> 'addr list \<times> bool \<Rightarrow> cname \<Rightarrow> 'heap \<times> 'addr list \<times> bool"
where
  "create_initial_object = 
  (\<lambda>(h, ads, b) C. 
     if b
     then let HA = allocate h (Class_type C)
          in if HA = {} then (h, ads, False)
             else let (h', a'') = SOME ha. ha \<in> HA in (h', ads @ [a''], True)
     else (h, ads, False))"

definition start_heap_data :: "'heap \<times> 'addr list \<times> bool"
where
  "start_heap_data = foldl create_initial_object (empty_heap, [], True) initialization_list"

definition start_heap :: 'heap
where "start_heap = fst start_heap_data"

definition start_heap_ok :: bool
where "start_heap_ok = snd (snd (start_heap_data))"

definition start_heap_obs :: "('addr, 'thread_id) obs_event list"
where
  "start_heap_obs =
  map (\<lambda>(C, a). NewHeapElem a (Class_type C)) (zip initialization_list (fst (snd start_heap_data)))"

definition start_addrs :: "'addr list"
where "start_addrs = fst (snd start_heap_data)"

definition addr_of_sys_xcpt :: "cname \<Rightarrow> 'addr"
where "addr_of_sys_xcpt C = the (map_of (zip initialization_list start_addrs) C)"

definition start_tid :: 'thread_id
where "start_tid = addr2thread_id (hd start_addrs)"

definition start_state :: "(cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'm \<Rightarrow> 'addr val list \<Rightarrow> 'x) \<Rightarrow> 'm prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> ('addr,'thread_id,'x,'heap,'addr) state"
where
  "start_state f P C M vs \<equiv>
   let (D, Ts, T, m) = method P C M
   in (K$ None, ([start_tid \<mapsto> (f D M Ts T (the m) vs, no_wait_locks)], start_heap), Map.empty, {})"

lemma create_initial_object_simps:
  "create_initial_object (h, ads, b) C = 
   (if b 
    then let HA = allocate h (Class_type C)
         in if HA = {} then (h, ads, False)
            else let (h', a'') = SOME ha. ha \<in> HA in (h', ads @ [a''], True)
    else (h, ads, False))"
unfolding create_initial_object_def by simp

lemma create_initial_object_False [simp]:
  "create_initial_object (h, ads, False) C = (h, ads, False)"
by(simp add: create_initial_object_simps)

lemma foldl_create_initial_object_False [simp]:
  "foldl create_initial_object (h, ads, False) Cs = (h, ads, False)"
by(induct Cs) simp_all

lemma NewHeapElem_start_heap_obs_start_addrsD:
  "NewHeapElem a CTn \<in> set start_heap_obs \<Longrightarrow> a \<in> set start_addrs"
unfolding start_heap_obs_def start_addrs_def
by(auto dest: set_zip_rightD)

lemma shr_start_state: "shr (start_state f P C M vs) = start_heap"
by(simp add: start_state_def split_beta)

lemma start_heap_obs_not_Read: 
  "ReadMem ad al v \<notin> set start_heap_obs"
unfolding start_heap_obs_def by auto

lemma length_initialization_list_le_length_start_addrs:
  "length initialization_list \<ge> length start_addrs"
proof -
  { fix h ads xs
    have "length (fst (snd (foldl create_initial_object (h, ads, True) xs))) \<le> length ads + length xs"
    proof(induct xs arbitrary: h ads)
      case Nil thus ?case by simp
    next
      case (Cons x xs)
      from this[of "fst (SOME ha. ha \<in> allocate h (Class_type x))" "ads @ [snd (SOME ha. ha \<in> allocate h (Class_type x))]"]
      show ?case by(clarsimp simp add: create_initial_object_simps split_beta)
    qed }
  from this[of empty_heap "[]" initialization_list]
  show ?thesis unfolding start_heap_def start_addrs_def start_heap_data_def by simp
qed

lemma (in -) distinct_initialization_list:
  "distinct initialization_list"
by(simp add: initialization_list_def sys_xcpts_list_def sys_xcpts_neqs Thread_neq_sys_xcpts)

lemma (in -) wf_syscls_initialization_list_is_class:
  "\<lbrakk> wf_syscls P; C \<in> set initialization_list \<rbrakk> \<Longrightarrow> is_class P C"
by(auto simp add: initialization_list_def sys_xcpts_list_def wf_syscls_is_class_xcpt)

lemma start_addrs_NewHeapElem_start_heap_obsD:
  "a \<in> set start_addrs \<Longrightarrow> \<exists>CTn. NewHeapElem a CTn \<in> set start_heap_obs"
using length_initialization_list_le_length_start_addrs
unfolding start_heap_obs_def start_addrs_def
by(force simp add: set_zip in_set_conv_nth intro: rev_image_eqI)

lemma in_set_start_addrs_conv_NewHeapElem:
  "a \<in> set start_addrs \<longleftrightarrow> (\<exists>CTn. NewHeapElem a CTn \<in> set start_heap_obs)"
by(blast dest: start_addrs_NewHeapElem_start_heap_obsD intro: NewHeapElem_start_heap_obs_start_addrsD)


subsection \<open>@{term preallocated}\<close>

definition preallocated :: "'heap \<Rightarrow> bool"
where "preallocated h \<equiv> \<forall>C \<in> sys_xcpts. typeof_addr h (addr_of_sys_xcpt C) = \<lfloor>Class_type C\<rfloor>"

lemma typeof_addr_sys_xcp: 
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> typeof_addr h (addr_of_sys_xcpt C) = \<lfloor>Class_type C\<rfloor>"
by(simp add: preallocated_def)

lemma typeof_sys_xcp:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr (addr_of_sys_xcpt C)) = \<lfloor>Class C\<rfloor>"
by(simp add: typeof_addr_sys_xcp)

lemma addr_of_sys_xcpt_start_addr:
  "\<lbrakk> start_heap_ok; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> addr_of_sys_xcpt C \<in> set start_addrs"
unfolding start_heap_ok_def start_heap_data_def initialization_list_def sys_xcpts_list_def 
  preallocated_def start_heap_def start_addrs_def
apply(simp split: prod.split_asm if_split_asm add: create_initial_object_simps)
apply(erule sys_xcpts_cases)
apply(simp_all add: addr_of_sys_xcpt_def start_addrs_def start_heap_data_def initialization_list_def sys_xcpts_list_def create_initial_object_simps)
done

lemma [simp]:
  assumes "preallocated h"
  shows typeof_ClassCast: "typeof_addr h (addr_of_sys_xcpt ClassCast) = Some(Class_type ClassCast)"
  and typeof_OutOfMemory: "typeof_addr h (addr_of_sys_xcpt OutOfMemory) = Some(Class_type OutOfMemory)" 
  and typeof_NullPointer: "typeof_addr h (addr_of_sys_xcpt NullPointer) = Some(Class_type NullPointer)" 
  and typeof_ArrayIndexOutOfBounds: 
  "typeof_addr h (addr_of_sys_xcpt ArrayIndexOutOfBounds) = Some(Class_type ArrayIndexOutOfBounds)" 
  and typeof_ArrayStore: "typeof_addr h (addr_of_sys_xcpt ArrayStore) = Some(Class_type ArrayStore)" 
  and typeof_NegativeArraySize: "typeof_addr h (addr_of_sys_xcpt NegativeArraySize) = Some(Class_type NegativeArraySize)" 
  and typeof_ArithmeticException: "typeof_addr h (addr_of_sys_xcpt ArithmeticException) = Some(Class_type ArithmeticException)" 
  and typeof_IllegalMonitorState: "typeof_addr h (addr_of_sys_xcpt IllegalMonitorState) = Some(Class_type IllegalMonitorState)"
  and typeof_IllegalThreadState: "typeof_addr h (addr_of_sys_xcpt IllegalThreadState) = Some(Class_type IllegalThreadState)" 
  and typeof_InterruptedException: "typeof_addr h (addr_of_sys_xcpt InterruptedException) = Some(Class_type InterruptedException)"
using assms
by(simp_all add: typeof_addr_sys_xcp)

lemma cname_of_xcp [simp]:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> cname_of h (addr_of_sys_xcpt C) = C"
by(drule (1) typeof_addr_sys_xcp)(simp add: cname_of_def)

lemma preallocated_hext:
  "\<lbrakk> preallocated h; h \<unlhd> h' \<rbrakk> \<Longrightarrow> preallocated h'"
by(auto simp add: preallocated_def dest: hext_objD)

end

context heap begin

lemma preallocated_heap_ops:
  assumes "preallocated h"
  shows preallocated_allocate: "\<And>a. (h', a) \<in> allocate h hT \<Longrightarrow> preallocated h'"
  and preallocated_write_field: "heap_write h a al v h' \<Longrightarrow> preallocated h'"
using preallocated_hext[OF assms, of h']
by(blast intro: hext_heap_ops)+

lemma not_empty_pairE: "\<lbrakk> A \<noteq> {}; \<And>a b. (a, b) \<in> A \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by auto

lemma allocate_not_emptyI: "(h', a) \<in> allocate h hT \<Longrightarrow> allocate h hT \<noteq> {}"
by auto

lemma allocate_Eps:
  "\<lbrakk> (h'', a'') \<in> allocate h hT; (SOME ha. ha \<in> allocate h hT) = (h', a') \<rbrakk> \<Longrightarrow> (h', a') \<in> allocate h hT"
by(drule sym)(auto intro: someI)

lemma preallocated_start_heap:
  "\<lbrakk> start_heap_ok; wf_syscls P \<rbrakk> \<Longrightarrow> preallocated start_heap"
unfolding start_heap_ok_def start_heap_data_def initialization_list_def sys_xcpts_list_def 
  preallocated_def start_heap_def start_addrs_def
apply(clarsimp split: prod.split_asm if_split_asm simp add: create_initial_object_simps)
apply(erule not_empty_pairE)+
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(drule (1) allocate_Eps)
apply(rotate_tac 13)
apply(frule allocate_SomeD, simp add: wf_syscls_is_class_xcpt, frule hext_allocate, rotate_tac 1)
apply(frule allocate_SomeD, simp add: wf_syscls_is_class_xcpt, frule hext_allocate, rotate_tac 1)
apply(frule allocate_SomeD, simp add: wf_syscls_is_class_xcpt, frule hext_allocate, rotate_tac 1)
apply(frule allocate_SomeD, simp add: wf_syscls_is_class_xcpt, frule hext_allocate, rotate_tac 1)
apply(frule allocate_SomeD, simp add: wf_syscls_is_class_xcpt, frule hext_allocate, rotate_tac 1)
apply(frule allocate_SomeD, simp add: wf_syscls_is_class_xcpt, frule hext_allocate, rotate_tac 1)
apply(frule allocate_SomeD, simp add: wf_syscls_is_class_xcpt, frule hext_allocate, rotate_tac 1)
apply(frule allocate_SomeD, simp add: wf_syscls_is_class_xcpt, frule hext_allocate, rotate_tac 1)
apply(frule allocate_SomeD, simp add: wf_syscls_is_class_xcpt, frule hext_allocate, rotate_tac 1)
apply(frule allocate_SomeD, simp add: wf_syscls_is_class_xcpt, frule hext_allocate, rotate_tac 1)
apply(frule allocate_SomeD, simp add: wf_syscls_is_class_xcpt, frule hext_allocate, rotate_tac 1)
apply(erule sys_xcpts_cases)
apply(simp_all add: addr_of_sys_xcpt_def initialization_list_def sys_xcpts_list_def sys_xcpts_neqs Thread_neq_sys_xcpts start_heap_data_def start_addrs_def create_initial_object_simps allocate_not_emptyI split del: if_split)
apply(assumption|erule typeof_addr_hext_mono)+
done

lemma start_tid_start_addrs:
  "\<lbrakk> wf_syscls P; start_heap_ok \<rbrakk> \<Longrightarrow> thread_id2addr start_tid \<in> set start_addrs"
unfolding start_heap_ok_def start_heap_data_def initialization_list_def sys_xcpts_list_def 
  preallocated_def start_heap_def start_addrs_def
apply(simp split: prod.split_asm if_split_asm add: create_initial_object_simps addr_of_sys_xcpt_def start_addrs_def start_tid_def start_heap_data_def initialization_list_def sys_xcpts_list_def)
apply(erule not_empty_pairE)+
apply(drule (1) allocate_Eps)
apply(rotate_tac -1)
apply(drule allocate_SomeD, simp)
apply(auto intro: addr2thread_id_inverse)
done

lemma
  assumes "wf_syscls P"
  shows dom_typeof_addr_start_heap: "set start_addrs \<subseteq> dom (typeof_addr start_heap)"
  and distinct_start_addrs: "distinct start_addrs"
proof -
  { fix h ads b and Cs xs :: "cname list"
    assume "set ads \<subseteq> dom (typeof_addr h)" and "distinct (Cs @ xs)" and "length Cs = length ads"
      and "\<And>C a. (C, a) \<in> set (zip Cs ads) \<Longrightarrow> typeof_addr h a = \<lfloor>Class_type C\<rfloor>"
      and "\<And>C. C \<in> set xs \<Longrightarrow> is_class P C"
    hence "set (fst (snd (foldl create_initial_object (h, ads, b) xs))) \<subseteq>
             dom (typeof_addr (fst (foldl create_initial_object (h, ads, b) xs))) \<and> 
           (distinct ads \<longrightarrow> distinct (fst (snd (foldl create_initial_object (h, ads, b) xs))))"
      (is "?concl xs h ads b Cs")
    proof(induct xs arbitrary: h ads b Cs)
      case Nil thus ?case by auto
    next
      case (Cons x xs)
      note ads = \<open>set ads \<subseteq> dom (typeof_addr h)\<close>
      note dist = \<open>distinct (Cs @ x # xs)\<close>
      note len = \<open>length Cs = length ads\<close>
      note type = \<open>\<And>C a. (C, a) \<in> set (zip Cs ads) \<Longrightarrow> typeof_addr h a = \<lfloor>Class_type C\<rfloor>\<close>
      note is_class = \<open>\<And>C. C \<in> set (x # xs) \<Longrightarrow> is_class P C\<close>
      show ?case
      proof(cases "b \<and> allocate h (Class_type x) \<noteq> {}")
        case False thus ?thesis
          using ads len by(auto simp add: create_initial_object_simps zip_append1)
      next
        case [simp]: True
        obtain h' a' where h'a': "(SOME ha. ha \<in> allocate h (Class_type x)) = (h', a')"
          by(cases "SOME ha. ha \<in> allocate h (Class_type x)")
        with True have new_obj: "(h', a') \<in> allocate h (Class_type x)"
          by(auto simp del: True intro: allocate_Eps)
        hence hext: "h \<unlhd> h'" by(rule hext_allocate)
        with ads new_obj have ads': "set ads \<subseteq> dom (typeof_addr h')"
          by(auto dest: typeof_addr_hext_mono[OF hext_allocate])
        moreover {
          from new_obj ads' is_class[of x]
          have "set (ads @ [a']) \<subseteq> dom (typeof_addr h')"
            by(auto dest: allocate_SomeD)
          moreover from dist have "distinct ((Cs @ [x]) @ xs)" by simp
          moreover have "length (Cs @ [x]) = length (ads @ [a'])" using len by simp
          moreover {
            fix C a
            assume "(C, a) \<in> set (zip (Cs @ [x]) (ads @ [a']))"
            hence "typeof_addr h' a = \<lfloor>Class_type C\<rfloor>"
              using hext new_obj type[of C a] len is_class
              by(auto dest: allocate_SomeD hext_objD) }
          note type' = this
          moreover have is_class': "\<And>C. C \<in> set xs \<Longrightarrow> is_class P C" using is_class by simp
          ultimately have "?concl xs h' (ads @ [a']) True (Cs @ [x])" by(rule Cons)
          moreover have "a' \<notin> set ads"
          proof
            assume a': "a' \<in> set ads"
            then obtain C where "(C, a') \<in> set (zip Cs ads)" "C \<in> set Cs"
              using len unfolding set_zip in_set_conv_nth by auto
            hence "typeof_addr h a' = \<lfloor>Class_type C\<rfloor>" by-(rule type)
            with hext have "typeof_addr h' a' = \<lfloor>Class_type C\<rfloor>" by(rule typeof_addr_hext_mono)
            moreover from new_obj is_class
            have "typeof_addr h' a' = \<lfloor>Class_type x\<rfloor>" by(auto dest: allocate_SomeD)
            ultimately have "C = x" by simp
            with dist \<open>C \<in> set Cs\<close> show False by simp
          qed
          moreover note calculation }
        ultimately show ?thesis by(simp add: create_initial_object_simps new_obj h'a')
      qed
    qed }
  from this[of "[]" empty_heap "[]" initialization_list True]
    distinct_initialization_list wf_syscls_initialization_list_is_class[OF assms]
  show "set start_addrs \<subseteq> dom (typeof_addr start_heap)"
    and "distinct start_addrs"
    unfolding start_heap_def start_addrs_def start_heap_data_def by auto
qed

lemma NewHeapElem_start_heap_obsD:
  assumes "wf_syscls P"
  and "NewHeapElem a hT \<in> set start_heap_obs"
  shows "typeof_addr start_heap a = \<lfloor>hT\<rfloor>"
proof -
  show ?thesis
  proof(cases hT)
    case (Class_type C)
    { fix h ads b xs Cs
      assume "(C, a) \<in> set (zip (Cs @ xs) (fst (snd (foldl create_initial_object (h, ads, b) xs))))"
        and "\<forall>(C, a) \<in> set (zip Cs ads). typeof_addr h a = \<lfloor>Class_type C\<rfloor>"
        and "length Cs = length ads"
        and "\<forall>C \<in> set xs. is_class P C"
      hence "typeof_addr (fst (foldl create_initial_object (h, ads, b) xs)) a = \<lfloor>Class_type C\<rfloor>"
      proof(induct xs arbitrary: h ads b Cs)
        case Nil thus ?case by auto
      next
        case (Cons x xs)
        note inv = \<open>\<forall>(C, a) \<in> set (zip Cs ads). typeof_addr h a = \<lfloor>Class_type C\<rfloor>\<close>
          and Ca = \<open>(C, a) \<in> set (zip (Cs @ x # xs) (fst (snd (foldl create_initial_object (h, ads, b) (x # xs)))))\<close>
          and len = \<open>length Cs = length ads\<close>
          and is_class = \<open>\<forall>C \<in> set (x # xs). is_class P C\<close>
        show ?case
        proof(cases "b \<and> allocate h (Class_type x) \<noteq> {}")
          case False thus ?thesis
            using inv Ca len by(auto simp add: create_initial_object_simps zip_append1 split: if_split_asm)
        next
          case [simp]: True
          obtain h' a' where h'a': "(SOME ha. ha \<in> allocate h (Class_type x)) = (h', a')"
            by(cases "SOME ha. ha \<in> allocate h (Class_type x)")
          with True have new_obj: "(h', a') \<in> allocate h (Class_type x)"
            by(auto simp del: True intro: allocate_Eps)
          hence hext: "h \<unlhd> h'" by(rule hext_allocate)

          have "(C, a) \<in> set (zip ((Cs @ [x]) @ xs) (fst (snd (foldl create_initial_object (h', ads @ [a'], True) xs))))"
            using Ca new_obj by(simp add: create_initial_object_simps h'a')
          moreover have "\<forall>(C, a)\<in>set (zip (Cs @ [x]) (ads @ [a'])).  typeof_addr h' a = \<lfloor>Class_type C\<rfloor>"
          proof(clarify)
            fix C a
            assume "(C, a) \<in> set (zip (Cs @ [x]) (ads @ [a']))"
            thus "typeof_addr h' a = \<lfloor>Class_type C\<rfloor>"
              using inv len hext new_obj is_class by(auto dest: allocate_SomeD typeof_addr_hext_mono)
          qed
          moreover have "length (Cs @ [x]) = length (ads @ [a'])" using len by simp
          moreover have "\<forall>C \<in> set xs. is_class P C" using is_class by simp
          ultimately have "typeof_addr (fst (foldl create_initial_object (h', ads @ [a'], True) xs)) a = \<lfloor>Class_type C\<rfloor>"
            by(rule Cons)
          thus ?thesis using new_obj by(simp add: create_initial_object_simps h'a')
        qed
      qed }
    from this[of "[]" initialization_list empty_heap "[]" True] assms wf_syscls_initialization_list_is_class[of P] 
    show ?thesis by(auto simp add: start_heap_obs_def start_heap_data_def start_heap_def Class_type)
  next
    case Array_type thus ?thesis using assms
      by(auto simp add: start_heap_obs_def start_heap_data_def start_heap_def)
  qed
qed

end


subsection \<open>Code generation\<close>

definition pick_addr :: "('heap \<times> 'addr) set \<Rightarrow> 'heap \<times> 'addr"
where "pick_addr HA = (SOME ha. ha \<in> HA)"

lemma pick_addr_code [code]:
  "pick_addr (set [ha]) = ha"
by(simp add: pick_addr_def)

lemma (in heap_base) start_heap_data_code:
  "start_heap_data = 
   (let 
     (h, ads, b) = foldl 
        (\<lambda>(h, ads, b) C. 
           if b then
             let HA = allocate h (Class_type C)
             in if HA = {} then (h, ads, False)
                else let (h', a'') = pick_addr HA in (h', a'' # ads, True)
           else (h, ads, False)) 
        (empty_heap, [], True) 
        initialization_list 
    in (h, rev ads, b))"
unfolding start_heap_data_def create_initial_object_def pick_addr_def
by(rule rev_induct)(simp_all add: split_beta)

lemmas [code] =
  heap_base.start_heap_data_code
  heap_base.start_heap_def
  heap_base.start_heap_ok_def
  heap_base.start_heap_obs_def
  heap_base.start_addrs_def
  heap_base.addr_of_sys_xcpt_def
  heap_base.start_tid_def
  heap_base.start_state_def

end
