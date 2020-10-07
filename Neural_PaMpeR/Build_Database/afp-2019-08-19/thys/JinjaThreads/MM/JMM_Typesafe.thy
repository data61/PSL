(*  Title:      JinjaThreads/MM/JMM_Typesafe.thy
    Author:     Andreas Lochbihler
*)

section \<open>Type-safety proof for the Java memory model\<close>

theory JMM_Typesafe 
imports
  JMM_Framework
begin

text \<open>
  Create a dynamic list \<open>heap_independent\<close> of theorems for replacing 
  heap-dependent constants by heap-independent ones. 
\<close>
ML \<open>
structure Heap_Independent_Rules = Named_Thms
(
  val name = @{binding heap_independent}
  val description = "Simplification rules for heap-independent constants"
)
\<close>
setup \<open>Heap_Independent_Rules.setup\<close>

locale heap_base' = 
  h: heap_base 
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate "\<lambda>_. typeof_addr" heap_read heap_write
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
begin

definition typeof_h :: "'addr val \<Rightarrow> ty option"
where "typeof_h = h.typeof_h undefined"
lemma typeof_h_conv_typeof_h [heap_independent, iff]: "h.typeof_h h = typeof_h"
by(rule ext)(case_tac x, simp_all add: typeof_h_def)
lemmas typeof_h_simps [simp] = h.typeof_h.simps [unfolded heap_independent]

definition cname_of :: "'addr \<Rightarrow> cname"
where "cname_of = h.cname_of undefined"
lemma cname_of_conv_cname_of [heap_independent, iff]: "h.cname_of h = cname_of"
by(simp add: cname_of_def h.cname_of_def[abs_def])

definition addr_loc_type :: "'m prog \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> ty \<Rightarrow> bool"
where "addr_loc_type P = h.addr_loc_type P undefined"
notation addr_loc_type ("_ \<turnstile> _@_ : _" [50, 50, 50, 50] 51)
lemma addr_loc_type_conv_addr_loc_type [heap_independent, iff]: 
  "h.addr_loc_type P h = addr_loc_type P"
by(simp add: addr_loc_type_def h.addr_loc_type_def)
lemmas addr_loc_type_cases [cases pred: addr_loc_type] = 
  h.addr_loc_type.cases[unfolded heap_independent]
lemmas addr_loc_type_intros = h.addr_loc_type.intros[unfolded heap_independent]

definition typeof_addr_loc :: "'m prog \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> ty"
where "typeof_addr_loc P = h.typeof_addr_loc P undefined"
lemma typeof_addr_loc_conv_typeof_addr_loc [heap_independent, iff]:
  "h.typeof_addr_loc P h = typeof_addr_loc P"
by(simp add: typeof_addr_loc_def h.typeof_addr_loc_def[abs_def])

definition conf :: "'a prog \<Rightarrow> 'addr val \<Rightarrow> ty \<Rightarrow> bool"
where "conf P \<equiv> h.conf P undefined"
notation conf ("_ \<turnstile> _ :\<le> _"  [51,51,51] 50)
lemma conf_conv_conf [heap_independent, iff]: "h.conf P h = conf P"
by(simp add: conf_def heap_base.conf_def[abs_def])
lemmas defval_conf [simp] = h.defval_conf[unfolded heap_independent]

definition lconf :: "'m prog \<Rightarrow> (vname \<rightharpoonup> 'addr val) \<Rightarrow> (vname \<rightharpoonup> ty) \<Rightarrow> bool" 
where "lconf P = h.lconf P undefined"
notation lconf ("_ \<turnstile> _ '(:\<le>') _" [51,51,51] 50)
lemma lconf_conv_lconf [heap_independent, iff]: "h.lconf P h = lconf P"
by(simp add: lconf_def h.lconf_def[abs_def])

definition confs :: "'m prog \<Rightarrow> 'addr val list \<Rightarrow> ty list \<Rightarrow> bool"
where "confs P = h.confs P undefined"
notation confs ("_ \<turnstile> _ [:\<le>] _" [51,51,51] 50)
lemma confs_conv_confs [heap_independent, iff]: "h.confs P h = confs P"
by(simp add: confs_def)

definition tconf :: "'m prog \<Rightarrow> 'thread_id \<Rightarrow> bool" 
where "tconf P = h.tconf P undefined"
notation tconf ("_ \<turnstile> _ \<surd>t" [51,51] 50)
lemma tconf_conv_tconf [heap_independent, iff]: "h.tconf P h = tconf P"
by(simp add: tconf_def h.tconf_def[abs_def])

definition vs_conf :: "'m prog \<Rightarrow> ('addr \<times> addr_loc \<Rightarrow> 'addr val set) \<Rightarrow> bool"
where "vs_conf P = h.vs_conf P undefined"
lemma vs_conf_conv_vs_conf [heap_independent, iff]: "h.vs_conf P h = vs_conf P"
by(simp add: vs_conf_def h.vs_conf_def[abs_def])

lemmas vs_confI = h.vs_confI[unfolded heap_independent]
lemmas vs_confD = h.vs_confD[unfolded heap_independent]

text \<open>
  use non-speculativity to express that only type-correct values are read
\<close>

primrec vs_type_all :: "'m prog \<Rightarrow> 'addr \<times> addr_loc \<Rightarrow> 'addr val set"
where "vs_type_all P (ad, al) = {v. \<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T}"

lemma vs_conf_vs_type_all [simp]: "vs_conf P (vs_type_all P)"
by(rule h.vs_confI[unfolded heap_independent])(simp)

lemma w_addrs_vs_type_all: "w_addrs (vs_type_all P) \<subseteq> dom typeof_addr"
by(auto simp add: w_addrs_def h.conf_def[unfolded heap_independent])

lemma w_addrs_vs_type_all_in_vs_type_all:
  "(\<Union>ad \<in> w_addrs (vs_type_all P). {(ad, al)|al. \<exists>T. P \<turnstile> ad@al : T}) \<subseteq> {adal. vs_type_all P adal \<noteq> {}}"
by(auto simp add: w_addrs_def vs_type_all_def intro: defval_conf)

declare vs_type_all.simps [simp del]

lemmas vs_conf_insert_iff = h.vs_conf_insert_iff[unfolded heap_independent]

end


locale heap' =
  h: heap
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate "\<lambda>_. typeof_addr" heap_read heap_write
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

sublocale heap' < heap_base' .

context heap' begin

lemma vs_conf_w_value_WriteMemD: 
  "\<lbrakk> vs_conf P (w_value P vs ob); ob = NormalAction (WriteMem ad al v) \<rbrakk>
  \<Longrightarrow> \<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T"
by(auto elim: vs_confD)

lemma vs_conf_w_values_WriteMemD:
  "\<lbrakk> vs_conf P (w_values P vs obs); NormalAction (WriteMem ad al v) \<in> set obs \<rbrakk>
  \<Longrightarrow> \<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T"
apply(induct obs arbitrary: vs)
apply(auto 4 3 elim: vs_confD intro: w_values_mono[THEN subsetD])
done

lemma w_values_vs_type_all_start_heap_obs:
  assumes wf: "wf_syscls P"
  shows "w_values P (vs_type_all P) (map snd (lift_start_obs h.start_tid h.start_heap_obs)) = vs_type_all P"
  (is "?lhs = ?rhs")
proof(rule antisym, rule le_funI, rule subsetI)
  fix adal v
  assume v: "v \<in> ?lhs adal"
  obtain ad al where adal: "adal = (ad, al)" by(cases adal)
  show "v \<in> ?rhs adal"
  proof(rule ccontr)
    assume v': "\<not> ?thesis"
    from in_w_valuesD[OF v[unfolded adal] this[unfolded adal]]
    obtain obs' wa obs''
      where eq: "map snd (lift_start_obs h.start_tid h.start_heap_obs) = obs' @ wa # obs''"
      and "write": "is_write_action wa"
      and loc: "(ad, al) \<in> action_loc_aux P wa"
      and vwa: "value_written_aux P wa al = v"
      by blast+
    from "write" show False
    proof cases
      case (WriteMem ad' al' v')
      with vwa loc eq have "WriteMem ad al v \<in> set h.start_heap_obs"
        by(auto simp add: map_eq_append_conv Cons_eq_append_conv lift_start_obs_def)
      from h.start_heap_write_typeable[OF this] v' adal
      show ?thesis by(auto simp add: vs_type_all_def)
    next
      case (NewHeapElem ad' hT)
      with vwa loc eq have "NewHeapElem ad hT \<in> set h.start_heap_obs"
        by(auto simp add: map_eq_append_conv Cons_eq_append_conv lift_start_obs_def)
      hence "typeof_addr ad = \<lfloor>hT\<rfloor>"
        by(rule h.NewHeapElem_start_heap_obsD[OF wf])
      with v' adal loc vwa NewHeapElem show ?thesis
        by(auto  simp add: vs_type_all_def intro: addr_loc_type_intros h.addr_loc_default_conf[unfolded heap_independent])
    qed
  qed
qed(rule w_values_greater)

end


lemma lprefix_lappend2I: "lprefix xs ys \<Longrightarrow> lprefix xs (lappend ys zs)"
by(auto simp add: lappend_assoc lprefix_conv_lappend)

locale known_addrs_typing' =
  h: known_addrs_typing
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate "\<lambda>_. typeof_addr" heap_read heap_write 
    allocated known_addrs 
    final r wfx
    P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool" 
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and known_addrs :: "'thread_id \<Rightarrow> 'x \<Rightarrow> 'addr set"
  and final :: "'x \<Rightarrow> bool"
  and r :: "('addr, 'thread_id, 'x, 'heap, 'addr, ('addr, 'thread_id) obs_event) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and wfx :: "'thread_id \<Rightarrow> 'x \<Rightarrow> 'heap \<Rightarrow> bool"
  and P :: "'md prog"
  +
  assumes NewHeapElem_typed: \<comment> \<open>Should this be moved to known\_addrs\_typing?\<close>
  "\<lbrakk> t \<turnstile> (x, h) -ta\<rightarrow> (x', h'); NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; typeof_addr ad \<noteq> None \<rbrakk>
  \<Longrightarrow> typeof_addr ad = \<lfloor>CTn\<rfloor>"

sublocale known_addrs_typing' < heap' by unfold_locales

context known_addrs_typing' begin

lemma known_addrs_typeable_in_vs_type_all:
  "h.if.known_addrs_state s \<subseteq> dom typeof_addr 
  \<Longrightarrow> (\<Union>a \<in> h.if.known_addrs_state s. {(a, al)|al. \<exists>T. P \<turnstile> a@al : T}) \<subseteq> {adal. vs_type_all P adal \<noteq> {}}"
by(auto 4 4 dest: subsetD simp add: vs_type_all.simps intro: defval_conf)

lemma if_NewHeapElem_typed: 
  "\<lbrakk> t \<turnstile> xh -ta\<rightarrow>i x'h'; NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; typeof_addr ad \<noteq> None \<rbrakk>
  \<Longrightarrow> typeof_addr ad = \<lfloor>CTn\<rfloor>"
by(cases rule: h.mthr.init_fin.cases)(auto dest: NewHeapElem_typed)

lemma if_redT_NewHeapElem_typed:
  "\<lbrakk> h.mthr.if.redT s (t, ta) s'; NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; typeof_addr ad \<noteq> None \<rbrakk>
  \<Longrightarrow> typeof_addr ad = \<lfloor>CTn\<rfloor>"
by(cases rule: h.mthr.if.redT.cases)(auto dest: if_NewHeapElem_typed)

lemma non_speculative_written_value_typeable:
  assumes wfx_start: "ts_ok wfx (thr (h.start_state f P C M vs)) h.start_heap" 
  and wfP: "wf_syscls P"
  and E: "E \<in> h.\<E>_start f P C M vs status"
  and "write": "w \<in> write_actions E"
  and adal: "(ad, al) \<in> action_loc P E w"
  and ns: "non_speculative P (vs_type_all P) (lmap snd (ltake (enat w) E))"
  shows "\<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> value_written P E w (ad, al) :\<le> T"
proof -
  let ?start_state = "init_fin_lift_state status (h.start_state f P C M vs)"
    and ?start_obs = "lift_start_obs h.start_tid h.start_heap_obs"
    and ?v = "value_written P E w (ad, al)"

  from "write" have iwa: "is_write_action (action_obs E w)" by cases

  from E obtain E' where E': "E = lappend (llist_of ?start_obs) E'"
    and \<E>: "E' \<in> h.mthr.if.\<E> ?start_state" by blast
  from \<E> obtain E'' where E'': "E' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E'')"
    and Runs: "h.mthr.if.mthr.Runs ?start_state E''"
    by-(rule h.mthr.if.\<E>.cases[OF \<E>])
  
  have wfx': "ts_ok (init_fin_lift wfx) (thr ?start_state) (shr ?start_state)"
    using wfx_start by(simp add: h.shr_start_state)

  from ns E'
  have ns: "non_speculative P (vs_type_all P) (lmap snd (ldropn (length (lift_start_obs h.start_tid h.start_heap_obs)) (ltake (enat w) E)))"
    by(subst (asm) lappend_ltake_ldrop[where n="enat (length (lift_start_obs h.start_tid h.start_heap_obs))", symmetric])(simp add: non_speculative_lappend min_def ltake_lappend1 w_values_vs_type_all_start_heap_obs[OF wfP] ldrop_enat split: if_split_asm)

  show ?thesis
  proof(cases "w < length ?start_obs")
    case True
    hence in_start: "action_obs E w \<in> set (map snd ?start_obs)"
      unfolding in_set_conv_nth E' by(simp add: lnth_lappend action_obs_def map_nth exI[where x="w"])
    
    from iwa show ?thesis
    proof(cases)
      case (WriteMem ad' al' v')
      with adal have "ad' = ad" "al' = al" "?v = v'" by(simp_all add: value_written.simps)
      with WriteMem in_start have "WriteMem ad al ?v \<in> set h.start_heap_obs" by auto
      thus ?thesis by(rule h.start_heap_write_typeable[unfolded heap_independent])
    next
      case (NewHeapElem ad' CTn)
      with adal have [simp]: "ad' = ad" by auto
      with NewHeapElem in_start have "NewHeapElem ad CTn \<in> set h.start_heap_obs" by auto
      with wfP have "typeof_addr ad = \<lfloor>CTn\<rfloor>" by(rule h.NewHeapElem_start_heap_obsD)
      with adal NewHeapElem show ?thesis
        by(cases al)(auto simp add: value_written.simps intro: addr_loc_type_intros h.addr_loc_default_conf[unfolded heap_independent])
    qed
  next
    case False
    define w' where "w' = w - length ?start_obs"
    with "write" False have w'_len: "enat w' < llength E'"
      by(cases "llength E'")(auto simp add: actions_def E' elim: write_actions.cases)
    with Runs obtain m_w n_w t_w ta_w 
      where E'_w: "lnth E' w' = (t_w, \<lbrace>ta_w\<rbrace>\<^bsub>o\<^esub> ! n_w)"
      and n_w: "n_w < length \<lbrace>ta_w\<rbrace>\<^bsub>o\<^esub>"
      and m_w: "enat m_w < llength E''"
      and w_sum: "w' = (\<Sum>i<m_w. length \<lbrace>snd (lnth E'' i)\<rbrace>\<^bsub>o\<^esub>) + n_w"
      and E''_m_w: "lnth E'' m_w = (t_w, ta_w)"
      unfolding E'' by(rule h.mthr.if.actions_\<E>E_aux)

    from E'_w have obs_w: "action_obs E w = \<lbrace>ta_w\<rbrace>\<^bsub>o\<^esub> ! n_w"
      using False E' w'_def by(simp add: action_obs_def lnth_lappend)
    
    let ?E'' = "ldropn (Suc m_w) E''"
    let ?m_E'' = "ltake (enat m_w) E''"
    have E'_unfold: "E'' = lappend ?m_E'' (LCons (lnth E'' m_w) ?E'')"
      unfolding ldropn_Suc_conv_ldropn[OF m_w] by simp
    hence "h.mthr.if.mthr.Runs ?start_state (lappend ?m_E'' (LCons (lnth E'' m_w) ?E''))"
      using Runs by simp
    then obtain \<sigma>' where \<sigma>_\<sigma>': "h.mthr.if.mthr.Trsys ?start_state (list_of ?m_E'') \<sigma>'"
      and Runs': "h.mthr.if.mthr.Runs \<sigma>' (LCons (lnth E'' m_w) ?E'')"
      by(rule h.mthr.if.mthr.Runs_lappendE) simp
    from Runs' obtain \<sigma>''' where red_w: "h.mthr.if.redT \<sigma>' (t_w, ta_w) \<sigma>'''"
      and Runs'': "h.mthr.if.mthr.Runs \<sigma>''' ?E''"
      unfolding E''_m_w by cases

    let ?EE'' = "lmap snd (lappend (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?m_E'')) (llist_of (map (Pair t_w) (take (n_w + 1) \<lbrace>ta_w\<rbrace>\<^bsub>o\<^esub>))))"
    have len_EE'': "llength ?EE'' = enat (w' + 1)" using n_w m_w
      apply(simp add: w_sum)
      apply(subst llength_lconcat_lfinite_conv_sum)
      apply(simp_all add: split_beta plus_enat_simps(1)[symmetric] add_Suc_right[symmetric] del: plus_enat_simps(1) add_Suc_right)
      apply(subst sum_hom[symmetric, where f=enat])
      apply(simp_all add: zero_enat_def min_def le_Suc_eq)
      apply(rule sum.cong)
      apply(auto simp add: lnth_ltake less_trans[where y="enat m_w"])
      done
    have prefix: "lprefix ?EE'' (lmap snd E')" unfolding E''
      by(subst (2) E'_unfold)(rule lmap_lprefix, clarsimp simp add: lmap_lappend_distrib E''_m_w lprefix_lappend2I[OF lprefix_llist_ofI[OF exI[where x="map (Pair t_w) (drop (n_w + 1) \<lbrace>ta_w\<rbrace>\<^bsub>o\<^esub>)"]]] map_append[symmetric])

    from iwa False have iwa': "is_write_action (action_obs E' w')" by(simp add: E' action_obs_def lnth_lappend w'_def)
    from ns False
    have "non_speculative P (vs_type_all P) (lmap snd (ltake (enat w') E'))"
      by(simp add: E' ltake_lappend lmap_lappend_distrib non_speculative_lappend ldropn_lappend2 w'_def)
    with iwa'
    have "non_speculative P (vs_type_all P) (lappend (lmap snd (ltake (enat w') E')) (LCons (action_obs E' w') LNil))"
      by cases(simp_all add: non_speculative_lappend)
    also have "lappend (lmap snd (ltake (enat w') E')) (LCons (action_obs E' w') LNil) = lmap snd (ltake (enat (w' + 1)) E')"
      using w'_len by(simp add: ltake_Suc_conv_snoc_lnth lmap_lappend_distrib action_obs_def)
    also {
      have "lprefix (lmap snd (ltake (enat (w' + 1)) E')) (lmap snd E')" by(rule lmap_lprefix) simp
      with prefix have "lprefix ?EE'' (lmap snd (ltake (enat (w' + 1)) E')) \<or> 
        lprefix (lmap snd (ltake (enat (w' + 1)) E')) ?EE''"
        by(rule lprefix_down_linear)
      moreover have "llength (lmap snd (ltake (enat (w' + 1)) E')) = enat (w' + 1)"
        using w'_len by(cases "llength E'") simp_all
      ultimately have "lmap snd (ltake (enat (w' + 1)) E') = ?EE''"
        using len_EE'' by(auto dest: lprefix_llength_eq_imp_eq) }
    finally
    have ns1: "non_speculative P (vs_type_all P) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?m_E''))))"
      and ns2: "non_speculative P (w_values P (vs_type_all P) (map snd (list_of (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?m_E''))))) (llist_of (take (Suc n_w) \<lbrace>ta_w\<rbrace>\<^bsub>o\<^esub>))"
      by(simp_all add: lmap_lappend_distrib non_speculative_lappend split_beta lconcat_llist_of[symmetric] lmap_lconcat llist.map_comp o_def split_def list_of_lmap[symmetric] del: list_of_lmap)

    have "vs_conf P (vs_type_all P)" by simp
    with \<sigma>_\<sigma>' wfx' ns1
    have wfx': "ts_ok (init_fin_lift wfx) (thr \<sigma>') (shr \<sigma>')"
      and vs_conf: "vs_conf P (w_values P (vs_type_all P) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?m_E''))))"
      by(rule h.if_RedT_non_speculative_invar[unfolded h.mthr.if.RedT_def heap_independent])+
    
    have "concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?m_E'')) = map snd (list_of (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?m_E'')))"
      by(simp add: split_def lmap_lconcat llist.map_comp o_def list_of_lconcat map_concat)
    with vs_conf have "vs_conf P (w_values P (vs_type_all P) \<dots>)" by simp
    with red_w wfx' ns2
    have vs_conf': "vs_conf P (w_values P (w_values P (vs_type_all P) (map snd (list_of (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?m_E''))))) (take (Suc n_w) \<lbrace>ta_w\<rbrace>\<^bsub>o\<^esub>))"
      (is "vs_conf _ ?vs'")
      by(rule h.if_redT_non_speculative_vs_conf[unfolded heap_independent])

    from len_EE'' have "enat w' < llength ?EE''" by simp
    from w'_len have "lnth ?EE'' w' = action_obs E' w'"
      using lprefix_lnthD[OF prefix \<open>enat w' < llength ?EE''\<close>] by(simp add: action_obs_def)
    hence "\<dots> \<in> lset ?EE''" using \<open>enat w' < llength ?EE''\<close> unfolding lset_conv_lnth by(auto intro!: exI)
    also have "\<dots> \<subseteq> set (map snd (list_of (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?m_E''))) @ take (Suc n_w) \<lbrace>ta_w\<rbrace>\<^bsub>o\<^esub>)"
      by(auto 4 4 intro: rev_image_eqI rev_bexI simp add: split_beta lset_lconcat_lfinite dest: lset_lappend[THEN subsetD])
    also have "action_obs E' w' = action_obs E w"
      using False by(simp add: E' w'_def lnth_lappend action_obs_def)
    also note obs_w_in_set = calculation and calculation = nothing

    from iwa have "?v \<in> w_values P (vs_type_all P) (map snd (list_of (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?m_E''))) @ take (Suc n_w) \<lbrace>ta_w\<rbrace>\<^bsub>o\<^esub>) (ad, al)"
    proof(cases)
      case (WriteMem ad' al' v')
      with adal have "ad' = ad" "al' = al" "?v = v'" by(simp_all add: value_written.simps)
      with obs_w_in_set WriteMem show ?thesis
        by -(rule w_values_WriteMemD, simp)
    next
      case (NewHeapElem ad' CTn)
      with adal have [simp]: "ad' = ad" and v: "?v = addr_loc_default P CTn al" 
        by(auto simp add: value_written.simps)
      with obs_w_in_set NewHeapElem adal show ?thesis
        by(unfold v)(rule w_values_new_actionD, simp_all)
    qed
    hence "?v \<in> ?vs' (ad, al)" by simp
    with vs_conf' show "\<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> ?v :\<le> T"
      by(rule h.vs_confD[unfolded heap_independent])
  qed
qed

lemma hb_read_value_typeable:
  assumes wfx_start: "ts_ok wfx (thr (h.start_state f P C M vs)) h.start_heap" 
    (is "ts_ok wfx (thr ?start_state) _")
  and wfP: "wf_syscls P"
  and E: "E \<in> h.\<E>_start f P C M vs status"
  and wf: "P \<turnstile> (E, ws) \<surd>"
  and races: "\<And>a ad al v. \<lbrakk> enat a < llength E; action_obs E a = NormalAction (ReadMem ad al v); \<not> P,E \<turnstile> ws a \<le>hb a \<rbrakk>
              \<Longrightarrow> \<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T"
  and r: "enat a < llength E"
  and read: "action_obs E a = NormalAction (ReadMem ad al v)"
  shows "\<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T"
using r read
proof(induction a arbitrary: ad al v rule: less_induct)
  case (less a)
  note r = \<open>enat a < llength E\<close>
    and read = \<open>action_obs E a = NormalAction (ReadMem ad al v)\<close>
  show ?case
  proof(cases "P,E \<turnstile> ws a \<le>hb a")
    case False with r read show ?thesis by(rule races)
  next
    case True
    note hb = this
    hence ao: "E \<turnstile> ws a \<le>a a" by(rule happens_before_into_action_order)

    from wf have ws: "is_write_seen P E ws" by(rule wf_exec_is_write_seenD)
    from r have "a \<in> actions E" by(simp add: actions_def)
    hence "a \<in> read_actions E" using read ..
    from is_write_seenD[OF ws this read]
    have "write": "ws a \<in> write_actions E" 
      and adal_w: "(ad, al) \<in> action_loc P E (ws a)"
      and written: "value_written P E (ws a) (ad, al) = v" by simp_all
    from "write" have iwa: "is_write_action (action_obs E (ws a))" by cases

    let ?start_state = "init_fin_lift_state status (h.start_state f P C M vs)"
      and ?start_obs = "lift_start_obs h.start_tid h.start_heap_obs"

    show ?thesis
    proof(cases "ws a < a")
      case True
      let ?EE'' = "lmap snd (ltake (enat (ws a)) E)"

      have "non_speculative P (vs_type_all P) ?EE''"
      proof(rule non_speculative_nthI)
        fix i ad' al' v'
        assume i: "enat i < llength ?EE''"
          and nth_i: "lnth ?EE'' i = NormalAction (ReadMem ad' al' v')"
        
        from i have "i < ws a" by simp
        hence i': "i < a" using True by(simp)
        moreover
        with r have "enat i < llength E" by(metis enat_ord_code(2) order_less_trans) 
        moreover
        with nth_i i \<open>i < ws a\<close>
        have "action_obs E i = NormalAction (ReadMem ad' al' v')"
          by(simp add: action_obs_def lnth_ltake ac_simps)
        ultimately have "\<exists>T. P \<turnstile> ad'@al' : T \<and> P \<turnstile> v' :\<le> T" by(rule less.IH)
        hence "v' \<in> vs_type_all P (ad', al')" by(simp add: vs_type_all.simps)
        thus "v' \<in> w_values P (vs_type_all P) (list_of (ltake (enat i) ?EE'')) (ad', al')"
          by(rule w_values_mono[THEN subsetD])
      qed
      with wfx_start wfP E "write" adal_w
      show ?thesis unfolding written[symmetric] by(rule non_speculative_written_value_typeable)
    next
      case False
      
      from E obtain E' where E': "E = lappend (llist_of ?start_obs) E'"
        and \<E>: "E' \<in> h.mthr.if.\<E> ?start_state" by blast
      from \<E> obtain E'' where E'': "E' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E'')"
        and Runs: "h.mthr.if.mthr.Runs ?start_state E''"
        by-(rule h.mthr.if.\<E>.cases[OF \<E>])

      have wfx': "ts_ok (init_fin_lift wfx) (thr ?start_state) (shr ?start_state)"
        using wfx_start by(simp add: h.shr_start_state)

      have a_start: "\<not> a < length ?start_obs"
      proof
        assume "a < length ?start_obs"
        with read have "NormalAction (ReadMem ad al v) \<in> snd ` set ?start_obs"
          unfolding set_map[symmetric] in_set_conv_nth
          by(auto simp add: E' lnth_lappend action_obs_def)
        hence "ReadMem ad al v \<in> set h.start_heap_obs" by auto
        thus False by(simp add: h.start_heap_obs_not_Read)
      qed
      hence ws_a_not_le: "\<not> ws a < length ?start_obs" using False by simp

      define w where "w = ws a - length ?start_obs"
      from "write" ws_a_not_le w_def
      have "enat w < llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E''))"
        by(cases "llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E''))")(auto simp add: actions_def E' E'' elim: write_actions.cases)
      with Runs obtain m_w n_w t_w ta_w 
        where E'_w: "lnth E' w = (t_w, \<lbrace>ta_w\<rbrace>\<^bsub>o\<^esub> ! n_w)"
        and n_w: "n_w < length \<lbrace>ta_w\<rbrace>\<^bsub>o\<^esub>"
        and m_w: "enat m_w < llength E''"
        and w_sum: "w = (\<Sum>i<m_w. length \<lbrace>snd (lnth E'' i)\<rbrace>\<^bsub>o\<^esub>) + n_w"
        and E''_m_w: "lnth E'' m_w = (t_w, ta_w)"
        unfolding E'' by(rule h.mthr.if.actions_\<E>E_aux)

      from E'_w have obs_w: "action_obs E (ws a) = \<lbrace>ta_w\<rbrace>\<^bsub>o\<^esub> ! n_w"
        using ws_a_not_le E' w_def by(simp add: action_obs_def lnth_lappend)

      let ?E'' = "ldropn (Suc m_w) E''"
      let ?m_E'' = "ltake (enat m_w) E''"
      have E'_unfold: "E'' = lappend ?m_E'' (LCons (lnth E'' m_w) ?E'')"
        unfolding ldropn_Suc_conv_ldropn[OF m_w] by simp
      hence "h.mthr.if.mthr.Runs ?start_state (lappend ?m_E'' (LCons (lnth E'' m_w) ?E''))"
        using Runs by simp
      then obtain \<sigma>' where \<sigma>_\<sigma>': "h.mthr.if.mthr.Trsys ?start_state (list_of ?m_E'') \<sigma>'"
        and Runs': "h.mthr.if.mthr.Runs \<sigma>' (LCons (lnth E'' m_w) ?E'')"
        by(rule h.mthr.if.mthr.Runs_lappendE) simp
      from Runs' obtain \<sigma>''' where red_w: "h.mthr.if.redT \<sigma>' (t_w, ta_w) \<sigma>'''"
        and Runs'': "h.mthr.if.mthr.Runs \<sigma>''' ?E''"
        unfolding E''_m_w by cases

      from "write" \<open>a \<in> read_actions E\<close> have "ws a \<noteq> a" by(auto dest: read_actions_not_write_actions)
      with False have "ws a > a" by simp
      with ao have new: "is_new_action (action_obs E (ws a))"
        by(simp add: action_order_def split: if_split_asm)
      then obtain CTn where obs_w': "action_obs E (ws a) = NormalAction (NewHeapElem ad CTn)" 
        using adal_w by cases auto

      define a' where "a' = a - length ?start_obs"
      with False w_def
      have "enat a' < llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E''))"
        by(simp add: le_less_trans[OF _ \<open>enat w < llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E''))\<close>])
      with Runs obtain m_a n_a t_a ta_a 
        where E'_a: "lnth E' a' = (t_a, \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> ! n_a)"
        and n_a: "n_a < length \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>"
        and m_a: "enat m_a < llength E''"
        and a_sum: "a' = (\<Sum>i<m_a. length \<lbrace>snd (lnth E'' i)\<rbrace>\<^bsub>o\<^esub>) + n_a"
        and E''_m_a: "lnth E'' m_a = (t_a, ta_a)"
        unfolding E'' by(rule h.mthr.if.actions_\<E>E_aux)
        
      from a_start E'_a read have obs_a: "\<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> ! n_a = NormalAction (ReadMem ad al v)"
        using E' w_def by(simp add: action_obs_def lnth_lappend a'_def)
      
      let ?E'' = "ldropn (Suc m_a) E''"
      let ?m_E'' = "ltake (enat m_a) E''"
      have E'_unfold: "E'' = lappend ?m_E'' (LCons (lnth E'' m_a) ?E'')"
        unfolding ldropn_Suc_conv_ldropn[OF m_a] by simp
      hence "h.mthr.if.mthr.Runs ?start_state (lappend ?m_E'' (LCons (lnth E'' m_a) ?E''))"
        using Runs by simp
      then obtain \<sigma>'' where \<sigma>_\<sigma>'': "h.mthr.if.mthr.Trsys ?start_state (list_of ?m_E'') \<sigma>''"
        and Runs'': "h.mthr.if.mthr.Runs \<sigma>'' (LCons (lnth E'' m_a) ?E'')"
        by(rule h.mthr.if.mthr.Runs_lappendE) simp
      from Runs'' obtain \<sigma>''' where red_a: "h.mthr.if.redT \<sigma>'' (t_a, ta_a) \<sigma>'''"
        and Runs'': "h.mthr.if.mthr.Runs \<sigma>''' ?E''"
        unfolding E''_m_a by cases

      let ?EE'' = "llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?m_E'')))"
      from m_a have "enat m_a \<le> llength E''" by simp
      hence len_EE'': "llength ?EE'' = enat (a' - n_a)"
        by(simp add: a_sum length_concat sum_list_sum_nth atLeast0LessThan length_list_of_conv_the_enat min_def split_beta lnth_ltake)
      have prefix: "lprefix ?EE'' (lmap snd E')" unfolding E''
        by(subst (2) E'_unfold)(simp add: lmap_lappend_distrib  lmap_lconcat llist.map_comp o_def split_def lconcat_llist_of[symmetric] lmap_llist_of[symmetric] lprefix_lappend2I del: lmap_llist_of)
      
      have ns: "non_speculative P (vs_type_all P) ?EE''"
      proof(rule non_speculative_nthI)
        fix i ad' al' v'
        assume i: "enat i < llength ?EE''"
          and lnth_i: "lnth ?EE'' i = NormalAction (ReadMem ad' al' v')"
          and "non_speculative P (vs_type_all P) (ltake (enat i) ?EE'')"
        
        let ?i = "i + length ?start_obs"
        
        from i len_EE'' have "i < a'" by simp
        hence i': "?i < a" by(simp add: a'_def)
        moreover
        hence "enat ?i < llength E" using \<open>enat a < llength E\<close> by(simp add: less_trans[where y="enat a"])
        moreover have "enat i < llength E'" using i
          by -(rule less_le_trans[OF _ lprefix_llength_le[OF prefix], simplified], simp)          
        from lprefix_lnthD[OF prefix i] lnth_i
        have "lnth (lmap snd E') i = NormalAction (ReadMem ad' al' v')" by simp
        hence "action_obs E ?i = NormalAction (ReadMem ad' al' v')" using \<open>enat i < llength E'\<close>
          by(simp add: E' action_obs_def lnth_lappend E'')
        ultimately have "\<exists>T. P \<turnstile> ad'@al' : T \<and> P \<turnstile> v' :\<le> T" by(rule less.IH)
        hence "v' \<in> vs_type_all P (ad', al')" by(simp add: vs_type_all.simps)
        thus "v' \<in> w_values P (vs_type_all P) (list_of (ltake (enat i) ?EE'')) (ad', al')"
          by(rule w_values_mono[THEN subsetD])
      qed
        
      have "vs_conf P (vs_type_all P)" by simp
      with \<sigma>_\<sigma>'' wfx' ns
      have wfx'': "ts_ok (init_fin_lift wfx) (thr \<sigma>'') (shr \<sigma>'')" 
        and vs'': "vs_conf P (w_values P (vs_type_all P) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?m_E''))))"
        by(rule h.if_RedT_non_speculative_invar[unfolded heap_independent h.mthr.if.RedT_def])+

      note red_w moreover
      from n_w obs_w obs_w' have "NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta_w\<rbrace>\<^bsub>o\<^esub>"
        unfolding in_set_conv_nth by auto
      moreover
      have ta_a_read: "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>"
        using n_a obs_a unfolding in_set_conv_nth by blast
      from red_a have "\<exists>T. P \<turnstile> ad@al : T"
      proof(cases)
        case (redT_normal x x' h')
        from wfx'' \<open>thr \<sigma>'' t_a = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
        have "init_fin_lift wfx t_a x (shr \<sigma>'')" by(rule ts_okD)
        with \<open>t_a \<turnstile> (x, shr \<sigma>'') -ta_a\<rightarrow>i (x', h')\<close>
        show ?thesis using ta_a_read
          by(rule h.init_fin_red_read_typeable[unfolded heap_independent])
      next
        case redT_acquire thus ?thesis using n_a obs_a ta_a_read by auto
      qed
      hence "typeof_addr ad \<noteq> None" by(auto elim: addr_loc_type_cases)
      ultimately have "typeof_addr ad = \<lfloor>CTn\<rfloor>" by(rule if_redT_NewHeapElem_typed)
      with written adal_w obs_w' show ?thesis
        by(cases al)(auto simp add: value_written.simps intro: addr_loc_type_intros h.addr_loc_default_conf[unfolded heap_independent])
    qed
  qed
qed

theorem 
  assumes wfx_start: "ts_ok wfx (thr (h.start_state f P C M vs)) h.start_heap" 
  and wfP: "wf_syscls P"
  and justified: "P \<turnstile> (E, ws) weakly_justified_by J"
  and J: "range (justifying_exec \<circ> J) \<subseteq> h.\<E>_start f P C M vs status"
  shows read_value_typeable_justifying:
    "\<lbrakk> 0 < n; enat a < llength (justifying_exec (J n));
      action_obs (justifying_exec (J n)) a = NormalAction (ReadMem ad al v) \<rbrakk>
    \<Longrightarrow> \<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T" 
  and read_value_typeable_justifed:
    "\<lbrakk> E \<in> h.\<E>_start f P C M vs status; P \<turnstile> (E, ws) \<surd>;
       enat a < llength E; action_obs E a = NormalAction (ReadMem ad al v) \<rbrakk>
    \<Longrightarrow> \<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T"
proof -
  let ?E = "\<lambda>n. justifying_exec (J n)"
    and ?\<phi> = "\<lambda>n. action_translation (J n)"
    and ?C = "\<lambda>n. committed (J n)"
    and ?ws = "\<lambda>n. justifying_ws (J n)"
  let ?\<E> = "h.\<E>_start f P C M vs status"
    and ?start_obs = "lift_start_obs h.start_tid h.start_heap_obs"
  { fix a n
    assume "enat a < llength (justifying_exec (J n))"
      and "action_obs (justifying_exec (J n)) a = NormalAction (ReadMem ad al v)"
      and "n > 0"
    thus "\<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T"
    proof(induction n arbitrary: a ad al v)
      case 0 thus ?case by simp
    next
      case (Suc n')
      define n where "n = Suc n'"
      with Suc have n: "0 < n" and a: "enat a < llength (?E n)"
        and a_obs: "action_obs (?E n) a = NormalAction (ReadMem ad al v)"
        by simp_all
      have wf_n: "P \<turnstile> (?E n, ?ws n) \<surd>"
        using justified by(simp add: justification_well_formed_def)
      from J have E: "?E n \<in> ?\<E>" 
        and E': "?E n' \<in> ?\<E>" by auto
      from a a_obs wfx_start wfP E wf_n show ?case
      proof(rule hb_read_value_typeable[rotated -2])
        fix a' ad' al' v'
        assume a': "enat a' < llength (?E n)"
          and a'_obs: "action_obs (?E n) a' = NormalAction (ReadMem ad' al' v')"
          and nhb: "\<not> P,?E n \<turnstile> ?ws n a' \<le>hb a'"
        from a' have "a' \<in> actions (?E n)" by(simp add: actions_def)
        hence read_a': "a' \<in> read_actions (?E n)" using a'_obs ..
        with justified nhb have committed': "?\<phi> n a' \<in> ?\<phi> n' ` ?C n'"
          unfolding is_weakly_justified_by.simps n_def uncommitted_reads_see_hb_def by blast

        from justified have wfa_n: "wf_action_translation E (J n)"
          and wfa_n': "wf_action_translation E (J n')" by(simp_all add: wf_action_translations_def)
        hence inj_n: "inj_on (?\<phi> n) (actions (?E n))"
          and inj_n': "inj_on (?\<phi> n') (actions (?E n'))"
          by(blast dest: wf_action_translation_on_inj_onD)+
        from justified have C_n: "?C n \<subseteq> actions (?E n)"
          and C_n': "?C n' \<subseteq> actions (?E n')"
          and wf_n': "P \<turnstile> (?E n', ?ws n') \<surd>"
          by(simp_all add: committed_subset_actions_def justification_well_formed_def)

        from justified have "?\<phi> n' ` ?C n' \<subseteq> ?\<phi> n ` ?C n"
          unfolding n_def by(simp add: is_commit_sequence_def)
        with n_def committed' have "?\<phi> n a' \<in> ?\<phi> n ` ?C n" by auto
        with inj_n C_n have committed: "a' \<in> ?C n"
          using \<open>a' \<in> actions (?E n)\<close> by(auto dest: inj_onD)
        with justified read_a' have ws_committed: "ws (?\<phi> n a') \<in> ?\<phi> n ` ?C n"
          by(rule weakly_justified_write_seen_hb_read_committed)

        from wf_n have ws_n: "is_write_seen P (?E n) (?ws n)" by(rule wf_exec_is_write_seenD)
        from is_write_seenD[OF this read_a' a'_obs]
        have ws_write: "?ws n a' \<in> write_actions (?E n)"
          and adal: "(ad', al') \<in> action_loc P (?E n) (?ws n a')"
          and written: "value_written P (?E n) (?ws n a') (ad', al') = v'" by simp_all

        define a'' where "a'' = inv_into (actions (?E n')) (?\<phi> n') (?\<phi> n a')"
        from C_n' n committed' have "?\<phi> n a' \<in> ?\<phi> n' ` actions (?E n')" by auto
        hence a'': "?\<phi> n' a'' = ?\<phi> n a'"
          and a''_action: "a'' \<in> actions (?E n')" using inj_n' committed' n
          by(simp_all add: a''_def f_inv_into_f inv_into_into)
        hence committed'': "a'' \<in> ?C n'" using committed' n inj_n' C_n' by(fastforce dest: inj_onD)

        from committed committed'' wfa_n wfa_n' a'' have "action_obs (?E n') a'' \<approx> action_obs (?E n) a'"
          by(auto dest!: wf_action_translation_on_actionD intro: sim_action_trans sim_action_sym)
        with a'_obs committed'' C_n' have read_a'': "a'' \<in> read_actions (?E n')"
          by(auto intro: read_actions.intros)

        then obtain ad'' al'' v'' 
          where a''_obs: "action_obs (?E n') a'' = NormalAction (ReadMem ad'' al'' v'')" by cases

        from committed'' have "n' > 0" using justified 
          by(cases n')(simp_all add: is_commit_sequence_def)
        then obtain n'' where n'': "n' = Suc n''" by(cases n') simp_all

        from justified have wfa_n'': "wf_action_translation E (J n'')" by(simp add: wf_action_translations_def)
        hence inj_n'': "inj_on (?\<phi> n'') (actions (?E n''))" by(blast dest: wf_action_translation_on_inj_onD)+
        from justified have C_n'': "?C n'' \<subseteq> actions (?E n'')" by(simp add: committed_subset_actions_def)

        from justified committed' committed'' n_def read_a' read_a'' n
        have "?\<phi> n (?ws n (inv_into (actions (?E n)) (?\<phi> n) (?\<phi> n' a''))) = ws (?\<phi> n' a'')"
          by(simp add: write_seen_committed_def)
        hence "?\<phi> n (?ws n a') = ws (?\<phi> n a')" using inj_n \<open>a' \<in> actions (?E n)\<close> by(simp add: a'')

        from ws_committed obtain w where w: "ws (?\<phi> n a') = ?\<phi> n w" 
          and committed_w: "w \<in> ?C n" by blast
        from committed_w C_n have "w \<in> actions (?E n)" by blast
        hence w_def: "w = ?ws n a'" using \<open>?\<phi> n (?ws n a') = ws (?\<phi> n a')\<close> inj_n ws_write
          unfolding w by(auto dest: inj_onD)
        have committed_ws: "?ws n a' \<in> ?C n" using committed_w by(simp add: w_def)

        with wfa_n have sim_ws: "action_obs (?E n) (?ws n a') \<approx> action_obs E (?\<phi> n (?ws n a'))"
          by(blast dest: wf_action_translation_on_actionD)

        from wfa_n committed_ws have sim_ws: "action_obs (?E n) (?ws n a') \<approx> action_obs E (?\<phi> n (?ws n a'))"
          by(blast dest: wf_action_translation_on_actionD)
        with adal have adal_E: "(ad', al') \<in> action_loc P E (?\<phi> n (?ws n a'))"
          by(simp add: action_loc_aux_sim_action)

        have "\<exists>w \<in> write_actions (?E n'). (ad', al') \<in> action_loc P (?E n') w \<and> value_written P (?E n') w (ad', al') = v'"
        proof(cases "?\<phi> n' a'' \<in> ?\<phi> n'' ` ?C n''")
          case True
          then obtain a''' where a''': "?\<phi> n'' a''' = ?\<phi> n' a''" 
            and committed''': "a''' \<in> ?C n''" by auto
          from committed''' C_n'' have a'''_action: "a''' \<in> actions (?E n'')" by auto
          
          from committed'' committed''' wfa_n' wfa_n'' a''' have "action_obs (?E n'') a''' \<approx> action_obs (?E n') a''"
            by(auto dest!: wf_action_translation_on_actionD intro: sim_action_trans sim_action_sym)
          with read_a'' committed''' C_n'' have read_a''': "a''' \<in> read_actions (?E n'')"
            by cases(auto intro: read_actions.intros)
          
          hence "?\<phi> n' (?ws n' (inv_into (actions (?E n')) (?\<phi> n') (?\<phi> n'' a'''))) = ws (?\<phi> n'' a''')"
            using justified committed'''
            unfolding is_weakly_justified_by.simps n'' Let_def write_seen_committed_def by blast
          also have "inv_into (actions (?E n')) (?\<phi> n') (?\<phi> n'' a''') = a''"
            using a''' inj_n' a''_action by(simp)
          also note a''' also note a''
          finally have \<phi>_n': "?\<phi> n' (?ws n' a'') = ws (?\<phi> n a')" .
          then have "ws (?\<phi> n a') = ?\<phi> n' (?ws n' a'')" ..
          with \<open>?\<phi> n (?ws n a') = ws (?\<phi> n a')\<close>[symmetric]
          have eq_ws: "?\<phi> n' (?ws n' a'') = ?\<phi> n (?ws n a')" by simp

          from wf_n'[THEN wf_exec_is_write_seenD, THEN is_write_seenD, OF read_a'' a''_obs]
          have ws_write': "?ws n' a'' \<in> write_actions (?E n')" by simp

          from justified read_a'' committed''
          have "ws (?\<phi> n' a'') \<in> ?\<phi> n' ` ?C n'" by(rule weakly_justified_write_seen_hb_read_committed)
          then obtain w' where w': "ws (?\<phi> n' a'') = ?\<phi> n' w'"
            and committed_w': "w' \<in> ?C n'" by blast
          from committed_w' C_n' have "w' \<in> actions (?E n')" by blast
          hence w'_def: "w' = ?ws n' a''" using \<phi>_n' inj_n' ws_write'
            unfolding w' a''[symmetric] by(auto dest: inj_onD)
          with committed_w' have committed_ws'': "?ws n' a'' \<in> committed (J n')" by simp
          with committed_ws wfa_n wfa_n' eq_ws
          have "action_obs (?E n') (?ws n' a'') \<approx> action_obs (?E n) (?ws n a')"
            by(auto dest!: wf_action_translation_on_actionD intro: sim_action_trans sim_action_sym)
          hence adal_eq: "action_loc P (?E n') (?ws n' a'') = action_loc P (?E n) (?ws n a')"
            by(simp add: action_loc_aux_sim_action)
          with adal have adal': "(ad', al') \<in> action_loc P (?E n') (?ws n' a'')" by(simp add: action_loc_aux_sim_action)
          
          from committed_ws'' have "?ws n' a'' \<in> actions (?E n')" using C_n' by blast
          with ws_write \<open>action_obs (?E n') (?ws n' a'') \<approx> action_obs (?E n) (?ws n a')\<close> 
          have ws_write'': "?ws n' a'' \<in> write_actions (?E n')" 
            by(cases)(auto intro: write_actions.intros simp add: sim_action_is_write_action_eq)
          from wfa_n' committed_ws''
          have sim_ws': "action_obs (?E n') (?ws n' a'') \<approx> action_obs E (?\<phi> n' (?ws n' a''))"
            by(blast dest: wf_action_translation_on_actionD)
          with adal' have adal'_E: "(ad', al') \<in> action_loc P E (?\<phi> n' (?ws n' a''))"
            by(simp add: action_loc_aux_sim_action)
          
          from justified committed_ws ws_write adal_E
          have "value_written P (?E n) (?ws n a') (ad', al') = value_written P E (?\<phi> n (?ws n a')) (ad', al')"
            unfolding is_weakly_justified_by.simps Let_def value_written_committed_def by blast
          also note eq_ws[symmetric]
          also from justified committed_ws'' ws_write'' adal'_E
          have "value_written P E (?\<phi> n' (?ws n' a'')) (ad', al') = value_written P (?E n') (?ws n' a'') (ad', al')"
            unfolding is_weakly_justified_by.simps Let_def value_written_committed_def by(blast dest: sym)
          finally show ?thesis using written ws_write'' adal' by auto
        next
          case False
          with justified read_a'' committed''
          have "ws (?\<phi> n' a'') \<in> ?\<phi> n'' ` ?C n''"
            unfolding is_weakly_justified_by.simps Let_def n'' committed_reads_see_committed_writes_weak_def by blast
          with a'' obtain w where w: "?\<phi> n'' w = ws (?\<phi> n a')"
            and committed_w: "w \<in> ?C n''" by auto
          from justified have "?\<phi> n'' ` ?C n'' \<subseteq> ?\<phi> n' ` ?C n'" by(simp add: is_commit_sequence_def n'')
          with committed_w w[symmetric] have "ws (?\<phi> n a') \<in> ?\<phi> n' ` ?C n'" by(auto)
          then obtain w' where w': "ws (?\<phi> n a') = ?\<phi> n' w'" and committed_w': "w' \<in> ?C n'" by blast
          from wfa_n' committed_w' have "action_obs (?E n') w' \<approx> action_obs E (?\<phi> n' w')"
            by(blast dest: wf_action_translation_on_actionD)
          from this[folded w', folded \<open>?\<phi> n (?ws n a') = ws (?\<phi> n a')\<close>] sim_ws[symmetric]
          have sim_w': "action_obs (?E n') w' \<approx> action_obs (?E n) (?ws n a')" by(rule sim_action_trans)
          with ws_write committed_w' C_n' have write_w': "w' \<in> write_actions (?E n')"
            by(cases)(auto intro!: write_actions.intros simp add: sim_action_is_write_action_eq)
          hence "value_written P (?E n') w' (ad', al') = value_written P E (?\<phi> n' w') (ad', al')"
            using adal_E committed_w' justified
            unfolding \<open>?\<phi> n (?ws n a') = ws (?\<phi> n a')\<close> w' is_weakly_justified_by.simps Let_def value_written_committed_def by blast
          also note w'[symmetric] 
          also note \<open>?\<phi> n (?ws n a') = ws (?\<phi> n a')\<close>[symmetric]
          also have "value_written P E (?\<phi> n (?ws n a')) (ad', al') = value_written P (?E n) (?ws n a') (ad', al')"
            using justified committed_ws ws_write adal_E 
            unfolding is_weakly_justified_by.simps Let_def value_written_committed_def by(blast dest: sym)
          also have "(ad', al') \<in> action_loc P (?E n') w'" using sim_w' adal by(simp add: action_loc_aux_sim_action)
          ultimately show ?thesis using written write_w' by auto
        qed
        then obtain w where w: "w \<in> write_actions (?E n')"
          and adal: "(ad', al') \<in> action_loc P (?E n') w"
          and written: "value_written P (?E n') w (ad', al') = v'" by blast
        from w have w_len: "enat w < llength (?E n')"
          by(cases)(simp add: actions_def)

        let ?EE'' = "lmap snd (ltake (enat w) (?E n'))"
        have "non_speculative P (vs_type_all P) ?EE''"
        proof(rule non_speculative_nthI)
          fix i ad al v
          assume i: "enat i < llength ?EE''"
            and i_nth: "lnth ?EE'' i = NormalAction (ReadMem ad al v)"
            and ns: "non_speculative P (vs_type_all P) (ltake (enat i) ?EE'')"

          from i w_len have "i < w" by(simp add: min_def not_le split: if_split_asm)
          with w_len have "enat i < llength (?E n')" by(simp add: less_trans[where y="enat w"])
          moreover
          from i_nth i \<open>i < w\<close> w_len
          have "action_obs (?E n') i = NormalAction (ReadMem ad al v)"
            by(simp add: action_obs_def ac_simps less_trans[where y="enat w"] lnth_ltake)
          moreover from n'' have "0 < n'" by simp
          ultimately have "\<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T" by(rule Suc.IH)
          hence "v \<in> vs_type_all P (ad, al)" by(simp add: vs_type_all.simps)
          thus "v \<in> w_values P (vs_type_all P) (list_of (ltake (enat i) ?EE'')) (ad, al)"
            by(rule w_values_mono[THEN subsetD])
        qed
        with wfx_start wfP E' w adal
        show "\<exists>T. P \<turnstile> ad'@al' : T \<and> P \<turnstile> v' :\<le> T"
          unfolding written[symmetric] by(rule non_speculative_written_value_typeable)
      qed
    qed
  }
  note justifying = this

  assume a: "enat a < llength E"
    and read: "action_obs E a = NormalAction (ReadMem ad al v)"
    and E: "E \<in> h.\<E>_start f P C M vs status"
    and wf: "P \<turnstile> (E, ws) \<surd>"
  from a have action: "a \<in> actions E" by(auto simp add: actions_def action_obs_def)
  with justified obtain n a' where a': "a = ?\<phi> n a'"
    and committed': "a' \<in> ?C n" by(auto simp add: is_commit_sequence_def)
  from justified have C_n: "?C n \<subseteq> actions (?E n)"
    and C_Sn: "?C (Suc n) \<subseteq> actions (?E (Suc n))"
    and wf_tr: "wf_action_translation E (J n)" 
    and wf_tr': "wf_action_translation E (J (Suc n))"
    by(auto simp add: committed_subset_actions_def wf_action_translations_def)
  from C_n committed' have action': "a' \<in> actions (?E n)" by blast
  from wf_tr committed' a'
  have "action_tid E a = action_tid (?E n) a'" "action_obs E a \<approx> action_obs (?E n) a'"
    by(auto simp add: wf_action_translation_on_def intro: sim_action_sym)
  with read obtain v'
    where "action_obs (?E n) a' = NormalAction (ReadMem ad al v')"
    by(clarsimp simp add: action_obs_def)
  with action' have read': "a' \<in> read_actions (?E n)" ..

  from justified have "?\<phi> n ` ?C n \<subseteq> ?\<phi> (Suc n) ` ?C (Suc n)"
    by(simp add: is_commit_sequence_def)
  with committed' a' have "a \<in> \<dots>" by auto
  then obtain a'' where a'': "a = ?\<phi> (Suc n) a''"
    and committed'': "a'' \<in> ?C (Suc n)" by auto
  from committed'' C_Sn have action'': "a'' \<in> actions (?E (Suc n))" by blast
  
  with wf_tr' have "a'' = inv_into (actions (?E (Suc n))) (?\<phi> (Suc n)) a"
    by(simp add: a'' wf_action_translation_on_def)
  with justified read' committed' a' have ws_a: "ws a = ?\<phi> (Suc n) (?ws (Suc n) a'')"
    by(simp add: write_seen_committed_def)

  from wf_tr' committed'' a''
  have "action_tid E a = action_tid (?E (Suc n)) a''"
    and "action_obs E a \<approx> action_obs (?E (Suc n)) a''"
    by(auto simp add: wf_action_translation_on_def intro: sim_action_sym)
  with read obtain v''
    where a_obs'': "action_obs (?E (Suc n)) a'' = NormalAction (ReadMem ad al v'')"
    by(clarsimp simp add: action_obs_def)
  with action'' have read'': "a'' \<in> read_actions (?E (Suc n))"
    by(auto intro: read_actions.intros simp add: action_obs_def)

  have "a \<in> read_actions E" "action_obs E a = NormalAction (ReadMem ad al v)"
    using action read by(auto intro: read_actions.intros simp add: action_obs_def read)
  from is_write_seenD[OF wf_exec_is_write_seenD[OF wf] this]
  have v_eq: "v = value_written P E (ws a) (ad, al)" 
    and adal: "(ad, al) \<in> action_loc P E (ws a)" by simp_all

  from justified have "P \<turnstile> (?E (Suc n), ?ws (Suc n)) \<surd>" by(simp add: justification_well_formed_def)
  from is_write_seenD[OF wf_exec_is_write_seenD[OF this] read'' a_obs'']
  have write'': "?ws (Suc n) a'' \<in> write_actions (?E (Suc n))" 
    and written'': "value_written P (?E (Suc n)) (?ws (Suc n) a'') (ad, al) = v''" 
    by simp_all

  from justified read'' committed'' 
  have "ws (?\<phi> (Suc n) a'') \<in> ?\<phi> (Suc n) ` ?C (Suc n)"
    by(rule weakly_justified_write_seen_hb_read_committed)
  then obtain w where w: "ws (?\<phi> (Suc n) a'') = ?\<phi> (Suc n) w"
    and committed_w: "w \<in> ?C (Suc n)" by blast
  with C_Sn have "w \<in> actions (?E (Suc n))" by blast
  moreover have "ws (?\<phi> (Suc n) a'') = ?\<phi> (Suc n) (?ws (Suc n) a'')"
    using ws_a a'' by simp
  ultimately have w_def: "w = ?ws (Suc n) a''"
    using wf_action_translation_on_inj_onD[OF wf_tr'] write''
    unfolding w by(auto dest: inj_onD)
  with committed_w have "?ws (Suc n) a'' \<in> ?C (Suc n)" by simp
  hence "value_written P E (ws a) (ad, al) = value_written P (?E (Suc n)) (?ws (Suc n) a'') (ad, al)"
    using adal justified write'' by(simp add: value_written_committed_def ws_a)
  with v_eq written'' have "v = v''" by simp

  from read'' have "enat a'' < llength (?E (Suc n))" by(cases)(simp add: actions_def)
  thus "\<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T"
    by(rule justifying)(simp_all add: a_obs'' \<open>v = v''\<close>)
qed

corollary weakly_legal_read_value_typeable:
  assumes wfx_start: "ts_ok wfx (thr (h.start_state f P C M vs)) h.start_heap" 
  and wfP: "wf_syscls P"
  and legal: "weakly_legal_execution P (h.\<E>_start f P C M vs status) (E, ws)"
  and a: "enat a < llength E"
  and read: "action_obs E a = NormalAction (ReadMem ad al v)"
  shows "\<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T"
proof -
  from legal obtain J 
    where "P \<turnstile> (E, ws) weakly_justified_by J"
    and "range (justifying_exec \<circ> J) \<subseteq> h.\<E>_start f P C M vs status"
    and "E \<in> h.\<E>_start f P C M vs status"
    and "P \<turnstile> (E, ws) \<surd>" by(rule legal_executionE)
  with wfx_start wfP show ?thesis using a read by(rule read_value_typeable_justifed)
qed

corollary legal_read_value_typeable:
  "\<lbrakk> ts_ok wfx (thr (h.start_state f P C M vs)) h.start_heap; wf_syscls P;
     legal_execution P (h.\<E>_start f P C M vs status) (E, ws);
     enat a < llength E; action_obs E a = NormalAction (ReadMem ad al v) \<rbrakk>
  \<Longrightarrow> \<exists>T. P \<turnstile> ad@al : T \<and> P \<turnstile> v :\<le> T"
by(erule (1) weakly_legal_read_value_typeable)(rule legal_imp_weakly_legal_execution)

end

end
