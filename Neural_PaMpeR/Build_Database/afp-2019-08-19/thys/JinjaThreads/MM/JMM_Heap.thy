(*  Title:      JinjaThreads/MM/JMM_Heap.thy
    Author:     Andreas Lochbihler
*)

section \<open>Locales for heap operations with set of allocated addresses\<close>

theory JMM_Heap 
imports
  "../Common/WellForm"
  SC_Completion
  HB_Completion
begin

definition w_addrs :: "('addr \<times> addr_loc \<Rightarrow> 'addr val set) \<Rightarrow> 'addr set"
where "w_addrs vs = {a. \<exists>adal. Addr a \<in> vs adal}"

lemma w_addrs_empty [simp]: "w_addrs (\<lambda>_. {}) = {}"
by(simp add: w_addrs_def)

locale allocated_heap_base = heap_base +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  fixes allocated :: "'heap \<Rightarrow> 'addr set"

locale allocated_heap = 
  allocated_heap_base +
  heap +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and P :: "'m prog"

  assumes allocated_empty: "allocated empty_heap = {}"
  and allocate_allocatedD:
  "(h', a) \<in> allocate h hT \<Longrightarrow> allocated h' = insert a (allocated h) \<and> a \<notin> allocated h"
  and heap_write_allocated_same:
  "heap_write h a al v h' \<Longrightarrow> allocated h' = allocated h"
begin

lemma allocate_allocated_mono: "(h', a) \<in> allocate h C \<Longrightarrow> allocated h \<subseteq> allocated h'"
by(simp_all add: allocate_allocatedD)

lemma
  shows start_addrs_allocated: "allocated start_heap = set start_addrs"
  and distinct_start_addrs': "distinct start_addrs"
proof -
  { fix h ads b and xs :: "cname list"
    let "?start_addrs h ads b xs" = "fst (snd (foldl create_initial_object (h, ads, b) xs))"
    let "?start_heap h ads b xs" = "fst (foldl create_initial_object (h, ads, b) xs)"
    assume "allocated h = set ads"
    hence "allocated (?start_heap h ads b xs) = set (?start_addrs h ads b xs) \<and>
           (distinct ads \<longrightarrow> distinct (?start_addrs h ads b xs))"
      (is "?concl xs h ads b")
    proof(induct xs arbitrary: h ads b)
      case Nil thus ?case by auto
    next
      case (Cons x xs)
      note ads = \<open>allocated h = set ads\<close>
      show ?case
      proof(cases "b \<and> allocate h (Class_type x) \<noteq> {}")
        case False thus ?thesis using ads
          by(simp add: create_initial_object_simps zip_append1)
      next
        case [simp]: True
        then obtain h' a' 
          where h'a': "(SOME ha. ha \<in> allocate h (Class_type x)) = (h', a')"
          and new_obj: "(h', a') \<in> allocate h (Class_type x)"
          by(cases "(SOME ha. ha \<in> allocate h (Class_type x))")(auto simp del: True dest: allocate_Eps)

        from new_obj have "allocated h' = insert a' (allocated h)" "a' \<notin> allocated h"
          by(auto dest: allocate_allocatedD)
        with ads have "allocated h' = set (ads @ [a'])" by auto
        hence "?concl xs h' (ads @ [a']) True" by(rule Cons)
        moreover have "a' \<notin> set ads" using \<open>a' \<notin> allocated h\<close> ads by blast
        ultimately show ?thesis by(simp add: create_initial_object_simps new_obj h'a')
      qed
    qed }
  from this[of empty_heap "[]" True initialization_list]
  show "allocated start_heap = set start_addrs"
    and distinct_start_addrs: "distinct start_addrs"
    unfolding start_heap_def start_addrs_def start_heap_data_def
    by(auto simp add: allocated_empty)
qed

lemma w_addrs_start_heap_obs: "w_addrs (w_values P vs (map NormalAction start_heap_obs)) \<subseteq> w_addrs vs"
proof -
  { fix xs
    let ?NewObj = "\<lambda>a C. NewHeapElem a (Class_type C) :: ('addr, 'thread_id) obs_event"
    let "?start_heap_obs xs" = "map (\<lambda>(C, a). ?NewObj a C) xs"
    have "w_addrs (w_values P vs (map NormalAction (?start_heap_obs xs))) \<subseteq> w_addrs vs"
      (is "?concl xs")
    proof(induct xs arbitrary: vs)
      case Nil thus ?case by simp
    next
      case (Cons x xs)
      have "w_addrs (w_values P vs (map NormalAction (map (\<lambda>(C, a). ?NewObj a C) (x # xs))))
        = w_addrs (w_values P (w_value P vs (NormalAction (?NewObj (snd x) (fst x)))) (map NormalAction (map (\<lambda>(C, a). ?NewObj a C) xs)))"
        by(simp add: split_beta)
      also have "\<dots> \<subseteq> w_addrs (w_value P vs (NormalAction (?NewObj (snd x) (fst x))))" by(rule Cons)
      also have "\<dots> \<subseteq> w_addrs vs"
        by(auto simp add: w_addrs_def default_val_not_Addr Addr_not_default_val)
      finally show ?case .
    qed }
  thus ?thesis by(simp add: start_heap_obs_def)
qed

end

context heap_base begin

lemma addr_loc_default_conf:
  "P \<turnstile> class_type_of CTn has F:T (fm) in C 
  \<Longrightarrow> P,h \<turnstile> addr_loc_default P CTn (CField C F) :\<le> T"
apply(cases CTn)
 apply simp
apply(frule has_field_decl_above)
apply simp
done

definition vs_conf :: "'m prog \<Rightarrow> 'heap \<Rightarrow> ('addr \<times> addr_loc \<Rightarrow> 'addr val set) \<Rightarrow> bool"
where "vs_conf P h vs \<longleftrightarrow> (\<forall>ad al v. v \<in> vs (ad, al) \<longrightarrow> (\<exists>T. P,h \<turnstile> ad@al : T \<and> P,h \<turnstile> v :\<le> T))"

lemma vs_confI:
  "(\<And>ad al v. v \<in> vs (ad, al) \<Longrightarrow> \<exists>T. P,h \<turnstile> ad@al : T \<and> P,h \<turnstile> v :\<le> T) \<Longrightarrow> vs_conf P h vs"
unfolding vs_conf_def by blast

lemma vs_confD:
  "\<lbrakk> vs_conf P h vs; v \<in> vs (ad, al) \<rbrakk> \<Longrightarrow> \<exists>T. P,h \<turnstile> ad@al : T \<and> P,h \<turnstile> v :\<le> T"
unfolding vs_conf_def by blast

lemma vs_conf_insert_iff:
  "vs_conf P h (vs((ad, al) := insert v (vs (ad, al)))) 
  \<longleftrightarrow> vs_conf P h vs \<and> (\<exists>T. P,h \<turnstile> ad@al : T \<and> P,h \<turnstile> v :\<le> T)"
by(auto 4 3 elim: vs_confD intro: vs_confI split: if_split_asm)

end

context heap begin

lemma vs_conf_hext: "\<lbrakk> vs_conf P h vs; h \<unlhd> h' \<rbrakk> \<Longrightarrow> vs_conf P h' vs"
by(blast intro!: vs_confI intro: conf_hext addr_loc_type_hext_mono dest: vs_confD)

lemma vs_conf_allocate:
  "\<lbrakk> vs_conf P h vs; (h', a) \<in> allocate h hT; is_htype P hT \<rbrakk> 
  \<Longrightarrow> vs_conf P h' (w_value P vs (NormalAction (NewHeapElem a hT)))"
apply(drule vs_conf_hext)
 apply(erule hext_allocate)
apply(auto intro!: vs_confI simp add: addr_locs_def split: if_split_asm htype.split_asm)
apply(auto 3 3 intro: addr_loc_type.intros defval_conf dest: allocate_SomeD elim: has_field_is_class vs_confD)
apply(rule exI conjI addr_loc_type.intros|drule allocate_SomeD|erule has_field_is_class|simp)+
done

end

text \<open>
  \<open>heap_read_typeable\<close> must not be defined in @{term heap_conf_base} (where it should be) because
  this would lead to duplicate definitions of \<open>heap_read_typeable\<close> in contexts where @{term heap_conf_base} 
  is imported twice with different parameters, e.g., @{term P} and @{term "J2JVM P"} in @{term "J_JVM_heap_conf_read"}.
\<close>

context heap_base begin

definition heap_read_typeable :: "('heap \<Rightarrow> bool) \<Rightarrow> 'm prog \<Rightarrow> bool"
where "heap_read_typeable hconf P \<longleftrightarrow> (\<forall>h ad al v T. hconf h \<longrightarrow> P,h \<turnstile> ad@al : T \<longrightarrow> P,h \<turnstile> v :\<le> T \<longrightarrow> heap_read h ad al v)"

lemma heap_read_typeableI:
  "(\<And>h ad al v T. \<lbrakk> P,h \<turnstile> ad@al : T; P,h \<turnstile> v :\<le> T; hconf h \<rbrakk> \<Longrightarrow> heap_read h ad al v) \<Longrightarrow> heap_read_typeable hconf P"
unfolding heap_read_typeable_def by blast

lemma heap_read_typeableD:
  "\<lbrakk> heap_read_typeable hconf P; P,h \<turnstile> ad@al : T; P,h \<turnstile> v :\<le> T; hconf h \<rbrakk> \<Longrightarrow> heap_read h ad al v"
unfolding heap_read_typeable_def by blast

end

context heap_base begin

definition heap_read_typed :: "'m prog \<Rightarrow> 'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
where "heap_read_typed P h ad al v \<longleftrightarrow> heap_read h ad al v \<and> (\<forall>T. P,h \<turnstile> ad@al : T \<longrightarrow> P,h \<turnstile> v :\<le> T)"

lemma heap_read_typedI:
  "\<lbrakk> heap_read h ad al v; \<And>T. P,h \<turnstile> ad@al : T \<Longrightarrow> P,h \<turnstile> v :\<le> T \<rbrakk> \<Longrightarrow> heap_read_typed P h ad al v"
unfolding heap_read_typed_def by blast

lemma heap_read_typed_into_heap_read:
  "heap_read_typed P h ad al v \<Longrightarrow> heap_read h ad al v"
unfolding heap_read_typed_def by blast

lemma heap_read_typed_typed:
  "\<lbrakk> heap_read_typed P h ad al v; P,h \<turnstile> ad@al : T \<rbrakk> \<Longrightarrow> P,h \<turnstile> v :\<le> T"
unfolding heap_read_typed_def by blast

end

context heap_conf begin

lemma heap_conf_read_heap_read_typed:
  "heap_conf_read addr2thread_id thread_id2addr empty_heap allocate typeof_addr (heap_read_typed P) heap_write hconf P"
proof
  fix h a al v T
  assume "heap_read_typed P h a al v" "P,h \<turnstile> a@al : T" 
  thus "P,h \<turnstile> v :\<le> T" by(rule heap_read_typed_typed)
qed

end

context heap begin

lemma start_addrs_dom_w_values:
  assumes wf: "wf_syscls P"
  and a: "a \<in> set start_addrs"
  and adal: "P,start_heap \<turnstile> a@al : T"
  shows "w_values P (\<lambda>_. {}) (map NormalAction start_heap_obs) (a, al) \<noteq> {}"
proof -
  from a obtain CTn where CTn: "NewHeapElem a CTn \<in> set start_heap_obs"
    unfolding in_set_start_addrs_conv_NewHeapElem ..
  then obtain obs obs' where obs: "start_heap_obs = obs @ NewHeapElem a CTn # obs'" by(auto dest: split_list)
  have "w_value P (w_values P (\<lambda>_. {}) (map NormalAction obs)) (NormalAction (NewHeapElem a CTn)) (a, al) \<noteq> {}"
  proof(cases CTn)
    case [simp]: (Class_type C)
    with wf CTn have "typeof_addr start_heap a = \<lfloor>Class_type C\<rfloor>"
      by(auto intro: NewHeapElem_start_heap_obsD)
    with adal show ?thesis by cases auto
  next
    case [simp]: (Array_type T n)
    with wf CTn have "typeof_addr start_heap a = \<lfloor>Array_type T n\<rfloor>"
      by(auto dest: NewHeapElem_start_heap_obsD)
    with adal show ?thesis by cases(auto dest: has_field_decl_above)
  qed
  moreover have "w_value P (w_values P (\<lambda>_. {}) (map NormalAction obs)) (NormalAction (NewHeapElem a CTn :: ('addr, 'thread_id) obs_event))
    (a, al) \<subseteq> w_values P (\<lambda>_. {}) (map NormalAction start_heap_obs) (a, al)"
    by(simp add: obs del: w_value.simps)(rule w_values_mono)
  ultimately show ?thesis by blast
qed

end

end
