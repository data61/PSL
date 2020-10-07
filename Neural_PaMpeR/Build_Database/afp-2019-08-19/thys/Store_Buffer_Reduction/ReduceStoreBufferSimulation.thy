(* Copyright (C) 2007--2010 Norbert Schirmer
 * All rights reserved, DFKI GmbH 
 *)
theory ReduceStoreBufferSimulation
imports ReduceStoreBuffer
begin

(* FIXME: a lot of theorems that now have sharing_consistent as precondition, may as well work with weak_sharing_consistent
 *)

locale initial\<^sub>s\<^sub>b = simple_ownership_distinct + read_only_unowned + unowned_shared +
constrains ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes empty_sb: "\<lbrakk>i < length ts; ts!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<rbrakk> \<Longrightarrow> sb=[]"
assumes empty_is: "\<lbrakk>i < length ts; ts!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<rbrakk> \<Longrightarrow> is=[]"
assumes empty_rels: "\<lbrakk>i < length ts; ts!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<rbrakk> \<Longrightarrow> \<R>=Map.empty"


sublocale initial\<^sub>s\<^sub>b \<subseteq> outstanding_non_volatile_refs_owned_or_read_only
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "non_volatile_owned_or_read_only False \<S> \<O> sb"
   using empty_sb [OF i_bound ts_i] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> outstanding_volatile_writes_unowned_by_others
proof
  fix i j p\<^sub>i is\<^sub>i \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j
  assume i_bound: "i < length ts" and 
    j_bound: "j < length ts" and
    neq_i_j: "i \<noteq> j" and
    ts_i: "ts ! i = (p\<^sub>i, is\<^sub>i, \<theta>\<^sub>i, sb\<^sub>i, \<D>\<^sub>i, \<O>\<^sub>i, \<R>\<^sub>i)" and
    ts_j: "ts ! j = (p\<^sub>j, is\<^sub>j, \<theta>\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j, \<R>\<^sub>j)" 
  show "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>i = {}"
  using empty_sb [OF i_bound ts_i] empty_sb [OF j_bound ts_j] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> read_only_reads_unowned
proof
  fix i j p\<^sub>i is\<^sub>i \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j
  assume i_bound: "i < length ts" and 
    j_bound: "j < length ts" and
    neq_i_j: "i \<noteq> j" and
    ts_i: "ts ! i = (p\<^sub>i, is\<^sub>i, \<theta>\<^sub>i, sb\<^sub>i, \<D>\<^sub>i, \<O>\<^sub>i, \<R>\<^sub>i)" and
    ts_j: "ts ! j = (p\<^sub>j, is\<^sub>j, \<theta>\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j, \<R>\<^sub>j)" 
  show "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> 
     read_only_reads (acquired True 
                          (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>i) \<O>\<^sub>i) 
                          (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>i) = {}"
  using empty_sb [OF i_bound ts_i] empty_sb [OF j_bound ts_j] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> ownership_distinct
proof
  fix i j p\<^sub>i is\<^sub>i \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j
  assume i_bound: "i < length ts" and 
    j_bound: "j < length ts" and
    neq_i_j: "i \<noteq> j" and
    ts_i: "ts ! i = (p\<^sub>i, is\<^sub>i, \<theta>\<^sub>i, sb\<^sub>i, \<D>\<^sub>i, \<O>\<^sub>i, \<R>\<^sub>i)" and
    ts_j: "ts ! j = (p\<^sub>j, is\<^sub>j, \<theta>\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j, \<R>\<^sub>j)" 
  show "(\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {}"
  using simple_ownership_distinct [OF i_bound j_bound neq_i_j ts_i ts_j] empty_sb [OF i_bound ts_i] empty_sb [OF j_bound ts_j]
  by auto
qed


sublocale initial\<^sub>s\<^sub>b \<subseteq> valid_ownership ..

sublocale initial\<^sub>s\<^sub>b \<subseteq> outstanding_non_volatile_writes_unshared
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "non_volatile_writes_unshared \<S> sb"
   using empty_sb [OF i_bound ts_i] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> sharing_consis
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "sharing_consistent \<S> \<O> sb"
   using empty_sb [OF i_bound ts_i] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> no_outstanding_write_to_read_only_memory
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "no_write_to_read_only_memory \<S> sb"
   using empty_sb [OF i_bound ts_i] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> valid_sharing ..
sublocale initial\<^sub>s\<^sub>b \<subseteq> valid_ownership_and_sharing ..

sublocale initial\<^sub>s\<^sub>b \<subseteq> load_tmps_distinct
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "distinct_load_tmps is"
   using empty_is [OF i_bound ts_i] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> read_tmps_distinct
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "distinct_read_tmps sb"
   using empty_sb [OF i_bound ts_i] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> load_tmps_read_tmps_distinct
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "load_tmps is \<inter> read_tmps sb = {}"
   using empty_sb [OF i_bound ts_i] empty_is [OF i_bound ts_i] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> load_tmps_read_tmps_distinct ..

sublocale initial\<^sub>s\<^sub>b \<subseteq> valid_write_sops
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "\<forall>sop \<in> write_sops sb. valid_sop sop"
   using empty_sb [OF i_bound ts_i] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> valid_store_sops
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "\<forall>sop \<in> store_sops is. valid_sop sop"
   using empty_is [OF i_bound ts_i] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> valid_sops ..

sublocale initial\<^sub>s\<^sub>b \<subseteq> valid_reads
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "reads_consistent False \<O> m sb"
   using empty_sb [OF i_bound ts_i] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> valid_history
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "program.history_consistent program_step \<theta> (hd_prog p sb) sb"
   using empty_sb [OF i_bound ts_i] by (auto simp add: program.history_consistent.simps)
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> valid_data_dependency
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "data_dependency_consistent_instrs (dom \<theta>) is"
   using empty_is [OF i_bound ts_i] by auto
next
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "load_tmps is \<inter> \<Union>(fst ` write_sops sb) = {}"
   using empty_is [OF i_bound ts_i] empty_sb [OF i_bound ts_i] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> load_tmps_fresh
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "load_tmps is \<inter> dom \<theta> = {}"
   using empty_is [OF i_bound ts_i] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> enough_flushs
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}"
   using empty_sb [OF i_bound ts_i] by auto
qed

sublocale initial\<^sub>s\<^sub>b \<subseteq> valid_program_history
proof
   fix i "is" \<O> \<R> \<D> \<theta> sb p sb\<^sub>1 sb\<^sub>2
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   assume sb: "sb=sb\<^sub>1@sb\<^sub>2"
   show "\<exists>isa. instrs sb\<^sub>2 @ is = isa @ prog_instrs sb\<^sub>2"
   using empty_sb [OF i_bound ts_i] empty_is [OF i_bound ts_i] sb by auto
next
   fix i "is" \<O> \<R> \<D> \<theta> sb p
   assume i_bound: "i < length ts"
   assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
   show "last_prog p sb = p"
   using empty_sb [OF i_bound ts_i] by auto
qed


inductive 
  sim_config:: "('p,'p store_buffer,bool,owns,rels) thread_config list \<times> memory \<times> shared \<Rightarrow> 
                ('p, unit,bool,owns,rels) thread_config list \<times> memory \<times> shared  \<Rightarrow> bool" 
 ("_ \<sim> _" [60,60] 100)
where
  "\<lbrakk>m = flush_all_until_volatile_write ts\<^sub>s\<^sub>b m\<^sub>s\<^sub>b;
    \<S> = share_all_until_volatile_write ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b;
    length ts\<^sub>s\<^sub>b = length ts; 
    \<forall>i < length ts\<^sub>s\<^sub>b. 
           let (p, is\<^sub>s\<^sub>b, \<theta>, sb, \<D>\<^sub>s\<^sub>b, \<O>, \<R>) = ts\<^sub>s\<^sub>b!i;
               suspends = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb
            in  \<exists>is \<D>. instrs suspends @ is\<^sub>s\<^sub>b = is @ prog_instrs suspends \<and>
                    \<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {}) \<and>
                ts!i = (hd_prog p suspends, 
                        is,
                        \<theta> |` (dom \<theta> - read_tmps suspends),(),
                        \<D>,  
                        acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>,
                        release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) (dom \<S>\<^sub>s\<^sub>b) \<R> )
   \<rbrakk> 
    \<Longrightarrow> 
     (ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<sim> (ts,m,\<S>)"

text \<open>The machine without
history only stores writes in the store-buffer.\<close>
inductive sim_history_config:: 
 "('p,'p store_buffer,'dirty,'owns,'rels) thread_config list \<Rightarrow> ('p,'p store_buffer,bool,owns,rels) thread_config list \<Rightarrow> bool" 
  ("_ \<sim>\<^sub>h _ " [60,60] 100)
where
  "\<lbrakk>length ts = length ts\<^sub>h; 
    \<forall>i < length ts. 
         (\<exists>\<O>' \<D>' \<R>'.
           let (p,is, \<theta>, sb,\<D>, \<O>,\<R>) = ts\<^sub>h!i in 
                ts!i=(p,is, \<theta>, filter is_Write\<^sub>s\<^sub>b sb,\<D>',\<O>',\<R>') \<and>
                (filter is_Write\<^sub>s\<^sub>b sb = [] \<longrightarrow> sb=[]))
   \<rbrakk> 
    \<Longrightarrow> 
     ts \<sim>\<^sub>h ts\<^sub>h"

lemma (in initial\<^sub>s\<^sub>b) history_refl:"ts \<sim>\<^sub>h ts"
apply -
apply (rule sim_history_config.intros)
apply  simp 
apply clarsimp
subgoal for i
apply (case_tac "ts!i")
apply (drule_tac  i=i in empty_sb)
apply  assumption
apply auto
done
done

lemma share_all_empty: "\<forall>i p is xs sb \<D> \<O> \<R>. i < length ts \<longrightarrow> ts!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<longrightarrow> sb=[]
  \<Longrightarrow> share_all_until_volatile_write ts \<S> = \<S>"
apply (induct ts)
apply  clarsimp
apply clarsimp
apply (frule_tac x=0 in spec)
apply clarsimp
apply force
done

lemma flush_all_empty: "\<forall>i p is xs sb \<D> \<O> \<R>. i < length ts \<longrightarrow> ts!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<longrightarrow> sb=[]
  \<Longrightarrow> flush_all_until_volatile_write ts m = m"
apply (induct ts)
apply  clarsimp
apply clarsimp
apply (frule_tac x=0 in spec)
apply clarsimp
apply force
done

lemma sim_config_emptyE: 
  assumes empty:
  "\<forall>i p is xs sb \<D> \<O> \<R>. i < length ts\<^sub>s\<^sub>b \<longrightarrow> ts\<^sub>s\<^sub>b!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<longrightarrow> sb=[]"
  assumes sim: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<sim> (ts,m,\<S>)"
  shows "\<S> = \<S>\<^sub>s\<^sub>b \<and> m = m\<^sub>s\<^sub>b \<and> length ts = length ts\<^sub>s\<^sub>b \<and>
         (\<forall>i < length ts\<^sub>s\<^sub>b. 
           let (p, is, \<theta>, sb, \<D>, \<O>, \<R>) = ts\<^sub>s\<^sub>b!i
            in ts!i = (p, is, \<theta>, (), \<D>, \<O>, \<R>))"
proof -
  from sim
  show ?thesis
  apply cases
  apply (clarsimp simp add: flush_all_empty [OF empty] share_all_empty [OF empty])
  subgoal for i
  apply (drule_tac x=i in spec)
  apply (cut_tac i=i in empty [rule_format])
  apply clarsimp
  apply assumption
  apply (auto simp add: Let_def)
  done
  done
qed

lemma sim_config_emptyI:
  assumes empty:
  "\<forall>i p is xs sb \<D> \<O> \<R>. i < length ts\<^sub>s\<^sub>b \<longrightarrow> ts\<^sub>s\<^sub>b!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<longrightarrow> sb=[]"
  assumes leq: "length ts = length ts\<^sub>s\<^sub>b"
  assumes ts: "(\<forall>i < length ts\<^sub>s\<^sub>b. 
           let (p, is, \<theta>, sb, \<D>, \<O>, \<R>) = ts\<^sub>s\<^sub>b!i
            in ts!i = (p, is, \<theta>, (), \<D>, \<O>, \<R>))"
  shows "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<sim> (ts,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b)"
apply (rule sim_config.intros) 
apply    (simp add: flush_all_empty [OF empty])
apply   (simp add: share_all_empty [OF empty])
apply  (simp add: leq)
apply (clarsimp)
apply (frule (1) empty [rule_format])
using ts
apply (auto simp add: Let_def)
done
lemma mem_eq_un_eq: "\<lbrakk>length ts'=length ts; \<forall>i< length ts'. P (ts'!i) = Q (ts!i) \<rbrakk> \<Longrightarrow> (\<Union>x\<in>set ts'. P x) = (\<Union>x\<in>set ts. Q x)"
apply (auto simp add: in_set_conv_nth )
apply  (force dest!: nth_mem)
apply (frule nth_mem)
subgoal for x i
apply (drule_tac x=i in spec)
apply auto
done
done

(* FIXME: move up *)
lemma (in program) trace_to_steps: 
assumes trace: "trace c 0 k" 
shows steps: "c 0 \<Rightarrow>\<^sub>d\<^sup>* c k"
using trace
proof (induct k)
  case 0
  show "c 0 \<Rightarrow>\<^sub>d\<^sup>* c 0"
    by auto
next
  case (Suc k)
  have prem: "trace c 0 (Suc k)" by fact
  hence "trace c 0 k" 
    by (auto simp add: program_trace_def)
  from Suc.hyps [OF this]
  have "c 0 \<Rightarrow>\<^sub>d\<^sup>* c k" .
  also
  term program_trace
  from prem interpret program_trace program_step  c 0 "Suc k" .
  from step [of k] have "c (k) \<Rightarrow>\<^sub>d c (Suc k)"
    by auto
  finally show ?case .
qed

lemma (in program) safe_reach_to_safe_reach_upto:
  assumes safe_reach: "safe_reach_direct safe c\<^sub>0"
  shows "safe_reach_upto n safe c\<^sub>0"
proof
  fix k c l
  assume k_n: "k \<le> n"
  assume trace: "trace c 0 k"
  assume c_0: "c 0 = c\<^sub>0"
  assume l_k: "l \<le> k"
  show "safe (c l)"
  proof -
    from trace k_n l_k have trace': "trace c 0 l"
      by (auto simp add: program_trace_def)
    from trace_to_steps [OF trace']
    have "c 0 \<Rightarrow>\<^sub>d\<^sup>* c l".
    with safe_reach c_0 show "safe (c l)"
    by (cases "c l") (auto simp add: safe_reach_def)
  qed
qed

lemma (in program_progress) safe_free_flowing_implies_safe_delayed':
  assumes init: "initial\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b"
  assumes sim: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<sim> (ts,m,\<S>)"
  assumes safe_reach_ff: "safe_reach_direct safe_free_flowing (ts,m,\<S>)"
  shows "safe_reach_direct safe_delayed (ts,m,\<S>)"
proof - 
  from init
  interpret ini: initial\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b .
  from sim obtain
   m: "m = flush_all_until_volatile_write ts\<^sub>s\<^sub>b m\<^sub>s\<^sub>b" and
   \<S>: "\<S> = share_all_until_volatile_write ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b" and
   leq: "length ts\<^sub>s\<^sub>b = length ts" and
   t_sim: "\<forall>i < length ts\<^sub>s\<^sub>b. 
           let (p, is\<^sub>s\<^sub>b, \<theta>, sb, \<D>\<^sub>s\<^sub>b, \<O>, \<R>) = ts\<^sub>s\<^sub>b!i;
               suspends = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb
            in  \<exists>is \<D>. instrs suspends @ is\<^sub>s\<^sub>b = is @ prog_instrs suspends \<and>
                    \<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {}) \<and>
                ts!i = (hd_prog p suspends, 
                        is,
                        \<theta> |` (dom \<theta> - read_tmps suspends),(),
                        \<D>,  
                        acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>,
                        release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) (dom \<S>\<^sub>s\<^sub>b) \<R> )"
    by cases auto

  from ini.empty_sb  
  have shared_eq: "\<S> = \<S>\<^sub>s\<^sub>b"
    apply (simp only: \<S>)
    apply (rule share_all_empty)
    apply force
    done
  have sd: "simple_ownership_distinct ts"
  proof 
    fix i j p\<^sub>i is\<^sub>i \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j
    assume i_bound: "i < length ts" and 
      j_bound: "j < length ts" and
      neq_i_j: "i \<noteq> j" and
      ts_i: "ts ! i = (p\<^sub>i, is\<^sub>i, \<theta>\<^sub>i, sb\<^sub>i, \<D>\<^sub>i, \<O>\<^sub>i, \<R>\<^sub>i)" and
      ts_j: "ts ! j = (p\<^sub>j, is\<^sub>j, \<theta>\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j, \<R>\<^sub>j)" 
    show "(\<O>\<^sub>i) \<inter> (\<O>\<^sub>j ) = {}"
    proof -
      from t_sim [simplified leq, rule_format, OF i_bound] ini.empty_sb [simplified leq, OF i_bound]
      have ts_i: "ts\<^sub>s\<^sub>b!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,[],\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
      using ts_i
        by (force simp add: Let_def)
      from t_sim [simplified leq, rule_format, OF j_bound] ini.empty_sb [simplified leq, OF j_bound]
      have ts_j: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,[],\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
      using ts_j
        by (force simp add: Let_def)
      from ini.simple_ownership_distinct [simplified leq, OF i_bound j_bound neq_i_j ts_i ts_j]
      show ?thesis .
    qed
  qed
  have ro: "read_only_unowned \<S> ts"
  proof 
    fix i "is" \<O> \<R> \<D> \<theta> sb p
    assume i_bound: "i < length ts"
    assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
    show "\<O> \<inter> read_only \<S> = {}"
    proof -
      from t_sim [simplified leq, rule_format, OF i_bound] ini.empty_sb [simplified leq, OF i_bound]
      have ts_i: "ts\<^sub>s\<^sub>b!i = (p,is,\<theta>,[],\<D>,\<O>,\<R>)"
      using ts_i
        by (force simp add: Let_def)
      from ini.read_only_unowned [simplified leq, OF i_bound ts_i] shared_eq
      show ?thesis by simp
    qed
  qed
  have us: "unowned_shared \<S> ts"
  proof 
    show "- (\<Union>((\<lambda>(_, _, _, _, _, \<O>, _). \<O>) ` set ts)) \<subseteq> dom \<S>"
    proof -
      have "(\<Union>((\<lambda>(_, _, _, _, _, \<O>, _). \<O>) ` set ts\<^sub>s\<^sub>b)) = (\<Union>((\<lambda>(_, _, _, _, _, \<O>, _). \<O>) ` set ts))"
        apply clarsimp
        apply (rule mem_eq_un_eq)
        apply (simp add: leq)
        apply clarsimp
        apply (frule t_sim [rule_format])
        apply (clarsimp simp add: Let_def)
        apply (drule (1) ini.empty_sb)
        apply auto
        done
      with ini.unowned_shared show ?thesis by (simp only: shared_eq)
    qed
  qed
  {
    fix i "is" \<O> \<R> \<D> \<theta> sb p
    assume i_bound: "i < length ts"
    assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
    have "\<R> = Map.empty"
    proof -
      from t_sim [simplified leq, rule_format, OF i_bound] ini.empty_sb [simplified leq, OF i_bound]
      have ts_i: "ts\<^sub>s\<^sub>b!i = (p,is,\<theta>,[],\<D>,\<O>,\<R>)"
      using ts_i
        by (force simp add: Let_def)
      from ini.empty_rels [simplified leq, OF i_bound ts_i]
      show ?thesis .
    qed
  }
  with us have initial: "initial (ts, m, \<S>)"
    by (fastforce simp add: initial_def)
  
  {
    fix ts' \<S>' m'
    assume steps: "(ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>')"
    have "safe_delayed (ts',m',\<S>')"
    proof -
      from steps_to_trace [OF steps] obtain c k
      where trace: "trace c 0 k" and c_0: "c 0 = (ts,m,\<S>)" and c_k: "c k = (ts',m',\<S>')"
        by auto
      from safe_reach_to_safe_reach_upto [OF safe_reach_ff]
      have safe_upto_k: "safe_reach_upto k safe_free_flowing (ts, m, \<S>)".
      from safe_free_flowing_implies_safe_delayed [OF _ _ _ _ safe_upto_k, simplified, OF initial sd ro us]
      have "safe_reach_upto k safe_delayed (ts, m, \<S>)".
      then interpret program_safe_reach_upto program_step k safe_delayed "(ts,m,\<S>)" .
      from safe_config [where c=c and k=k and l=k, OF _ trace c_0] c_k show ?thesis by simp
    qed
  }
  then show ?thesis
    by (clarsimp simp add: safe_reach_def)
qed

(* FIXME: move up *)
lemma map_onws_sb_owned:"\<And>j. j < length ts \<Longrightarrow> map \<O>_sb ts ! j = (\<O>\<^sub>j,sb\<^sub>j) \<Longrightarrow> map owned ts ! j = \<O>\<^sub>j"
apply (induct ts)
apply  simp 
subgoal for t ts j
apply (case_tac j)
apply  (case_tac t)
apply  auto
done
done


lemma map_onws_sb_owned':"\<And>j. j < length ts \<Longrightarrow> \<O>_sb (ts ! j) = (\<O>\<^sub>j,sb\<^sub>j) \<Longrightarrow> owned (ts ! j) = \<O>\<^sub>j"
apply (induct ts)
apply  simp
subgoal for t ts j
apply (case_tac j)
apply  (case_tac t)
apply  auto
done
done

(* FIXME: substitutes in application below: read_only_read_acquired_unforwarded_witness*)
lemma read_only_read_acquired_unforwarded_acquire_witness:
  "\<And>\<S> \<O> X.\<lbrakk>non_volatile_owned_or_read_only True \<S> \<O> sb;
 sharing_consistent \<S> \<O> sb; a \<notin> read_only \<S>; a \<notin> \<O>;
 a \<in> unforwarded_non_volatile_reads sb X\<rbrakk>
\<Longrightarrow>(\<exists>sop a' v ys zs A L R W. 
     sb = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W # zs \<and> 
     a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys \<and> a' \<noteq> a) \<or>
(\<exists>A L R W ys zs. sb = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys)"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain 
	nvo': "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and
	a_nro: "a \<notin> read_only \<S>" and
	a_unowned: "a \<notin> \<O>" and
	A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and
	R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and 
	a_unforw: "a \<in> unforwarded_non_volatile_reads sb (insert a' X)" 
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      from unforwarded_not_written [OF a_unforw]
      have a_notin: "a \<notin> insert a' X".
      hence a'_a: "a' \<noteq> a"
        by simp
      from R_owns a_unowned
      have a_R: "a \<notin> R"
	by auto
      show ?thesis
      proof (cases "a \<in> A")
	case True
	then show ?thesis
	  apply -
	  apply (rule disjI1)
	  apply (rule_tac x=sop in exI)
	  apply (rule_tac x=a' in exI)	
	  apply (rule_tac x=v in exI)	
	  apply (rule_tac x="[]" in exI)	
	  apply (rule_tac x=sb in exI)	
	  apply (simp add: Write\<^sub>s\<^sub>b volatile True a'_a)
	  done
      next
	case False
	with a_unowned R_owns a_nro L_A A_R
	obtain a_nro': "a \<notin> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and a_unowned': "a \<notin> \<O> \<union> A - R"
	  by (force simp add: in_read_only_convs)

	from Cons.hyps [OF nvo' consis' a_nro' a_unowned' a_unforw]
	have "(\<exists>sop a' v ys zs A L R W.
                 sb = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W # zs \<and>
                 a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys \<and> a' \<noteq> a) \<or>
              (\<exists>A L R W ys zs. sb = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys)"
              (is "?write \<or> ?ghst")
	  by simp
	then show ?thesis
        proof 
	  assume ?write

	  then obtain sop' a'' v' ys zs A' L' R' W' where 
            sb: "sb = ys @ Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs" and
            props: "a \<in> A'" "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys \<and> a'' \<noteq> a"
	    by auto
	  
	  
	  show ?thesis
	  using props False a_notin sb
	    apply -
	    apply (rule disjI1)
	    apply (rule_tac x=sop' in exI)
	    apply (rule_tac x=a'' in exI)	
	    apply (rule_tac x=v' in exI)	
	    apply (rule_tac x="(x#ys)" in exI)	
	    apply (rule_tac x=zs in exI)	
	    apply (simp add: Write\<^sub>s\<^sub>b volatile False a'_a)
	    done
	next
	  assume ?ghst
	  then obtain ys zs A' L' R' W'  where 
            sb: "sb = ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs" and
            props: "a \<in> A'" "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys"
	    by auto
	  
	  
	  show ?thesis
	  using props False a_notin sb
	    apply -
	    apply (rule disjI2)
	    apply (rule_tac x=A' in exI)
	    apply (rule_tac x=L' in exI)	
	    apply (rule_tac x=R' in exI)
	    apply (rule_tac x=W' in exI)	
	    apply (rule_tac x="(x#ys)" in exI)	
	    apply (rule_tac x=zs in exI)	
	    apply (simp add: Write\<^sub>s\<^sub>b volatile False a'_a)
	    done
	qed
      qed
    next
      case False
      from Cons.prems obtain 
	consis': "sharing_consistent \<S> \<O> sb" and
	a_nro': "a \<notin> read_only \<S>" and
	a_unowned: "a \<notin> \<O>" and
	a_ro': "a' \<in> \<O>" and
	nvo': "non_volatile_owned_or_read_only True \<S> \<O> sb" and
	a_unforw': "a \<in> unforwarded_non_volatile_reads sb (insert a' X)"
	by (auto simp add: Write\<^sub>s\<^sub>b False split: if_split_asm)
      
      from unforwarded_not_written [OF a_unforw']
      have a_notin: "a \<notin> insert a' X".

      from Cons.hyps [OF nvo' consis' a_nro' a_unowned a_unforw']
      have "(\<exists>sop a' v ys zs A L R W.
                 sb = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W # zs \<and>
                 a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys \<and> a' \<noteq> a) \<or>
              (\<exists>A L R W ys zs. sb = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys)"
        (is "?write \<or> ?ghst")
	by simp
	then show ?thesis
        proof 
	  assume ?write

	  then obtain sop' a'' v' ys zs A' L' R' W' where 
            sb: "sb = ys @ Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs" and
            props: "a \<in> A'" "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys \<and> a'' \<noteq> a"
	    by auto
	  
	  
	  show ?thesis
	  using props False a_notin sb
	    apply -
	    apply (rule disjI1)
	    apply (rule_tac x=sop' in exI)
	    apply (rule_tac x=a'' in exI)	
	    apply (rule_tac x=v' in exI)	
	    apply (rule_tac x="(x#ys)" in exI)	
	    apply (rule_tac x=zs in exI)	
	    apply (simp add: Write\<^sub>s\<^sub>b False )
	    done
	next
	  assume ?ghst
	  then obtain ys zs A' L' R' W'  where 
            sb: "sb = ys @ Ghost\<^sub>s\<^sub>b A' L' R' W' # zs" and
            props: "a \<in> A'" "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys"
	    by auto
	  
	  
	  show ?thesis
	  using props False a_notin sb
	    apply -
	    apply (rule disjI2)
	    apply (rule_tac x=A' in exI)
	    apply (rule_tac x=L' in exI)
	    apply (rule_tac x=R' in exI)
	    apply (rule_tac x=W' in exI)
	    apply (rule_tac x="(x#ys)" in exI)	
	    apply (rule_tac x=zs in exI)	
	    apply (simp add: Write\<^sub>s\<^sub>b False )
	    done
	qed
      qed
    next
    case (Read\<^sub>s\<^sub>b volatile a' t v)
    from Cons.prems
    obtain 	
      consis': "sharing_consistent \<S> \<O> sb" and
      a_nro': "a \<notin> read_only \<S>" and
      a_unowned: "a \<notin> \<O>" and
      nvo': "non_volatile_owned_or_read_only True \<S> \<O> sb" and 
      a_unforw: "a \<in> unforwarded_non_volatile_reads sb X"
      by (auto simp add: Read\<^sub>s\<^sub>b split: if_split_asm)
    from Cons.hyps [OF nvo' consis' a_nro' a_unowned a_unforw]
    have "(\<exists>sop a' v ys zs A L R W.
                 sb = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W # zs \<and>
                 a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys \<and> a' \<noteq> a) \<or>
              (\<exists>A L R W ys zs. sb = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys)"
      (is "?write \<or> ?ghst")
      by simp
    then show ?thesis
    proof 
      assume ?write

      then obtain sop' a'' v' ys zs A' L' R' W' where 
        sb: "sb = ys @ Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs" and
        props: "a \<in> A'" "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys \<and> a'' \<noteq> a"
        by auto
	  
	  
      show ?thesis
      using props sb
        apply -
	apply (rule disjI1)
	apply (rule_tac x=sop' in exI)
	apply (rule_tac x=a'' in exI)	
	apply (rule_tac x=v' in exI)	
	apply (rule_tac x="(x#ys)" in exI)	
	apply (rule_tac x=zs in exI)	
	apply (simp add: Read\<^sub>s\<^sub>b)
	done
    next
      assume ?ghst
      then obtain ys zs A' L' R' W' where 
        sb: "sb = ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs" and
        props: "a \<in> A'" "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys"
        by auto
	  
	  
      show ?thesis
      using props sb
      apply -
      apply (rule disjI2)
      apply (rule_tac x=A' in exI)
      apply (rule_tac x=L' in exI)	
      apply (rule_tac x=R' in exI)
      apply (rule_tac x=W' in exI)	
      apply (rule_tac x="(x#ys)" in exI)	
      apply (rule_tac x=zs in exI)	
      apply (simp add: Read\<^sub>s\<^sub>b )
      done
    qed
  next
    case Prog\<^sub>s\<^sub>b
    from Cons.prems
    obtain 	
      consis': "sharing_consistent \<S> \<O> sb" and
      a_nro': "a \<notin> read_only \<S>" and
      a_unowned: "a \<notin> \<O>" and
      nvo': "non_volatile_owned_or_read_only True \<S> \<O> sb" and 
      a_unforw: "a \<in> unforwarded_non_volatile_reads sb X"
      by (auto simp add: Prog\<^sub>s\<^sub>b)
    from Cons.hyps [OF nvo' consis' a_nro' a_unowned a_unforw]
    have "(\<exists>sop a' v ys zs A L R W.
                 sb = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W # zs \<and>
                 a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys \<and> a' \<noteq> a) \<or>
              (\<exists>A L R W ys zs. sb = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys)"
      (is "?write \<or> ?ghst")
      by simp
    then show ?thesis
    proof 
      assume ?write

      then obtain sop' a'' v' ys zs A' L' R' W' where 
        sb: "sb = ys @ Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs" and
        props: "a \<in> A'" "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys \<and> a'' \<noteq> a"
        by auto
	  
	  
      show ?thesis
      using props sb
        apply -
	apply (rule disjI1)
	apply (rule_tac x=sop' in exI)
	apply (rule_tac x=a'' in exI)	
	apply (rule_tac x=v' in exI)	
	apply (rule_tac x="(x#ys)" in exI)	
	apply (rule_tac x=zs in exI)	
	apply (simp add: Prog\<^sub>s\<^sub>b)
	done
    next
      assume ?ghst
      then obtain ys zs A' L' R' W' where 
        sb: "sb = ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs" and
        props: "a \<in> A'" "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys"
        by auto
	  
	  
      show ?thesis
      using props sb
      apply -
      apply (rule disjI2)
      apply (rule_tac x=A' in exI)
      apply (rule_tac x=L' in exI)	
      apply (rule_tac x=R' in exI)
      apply (rule_tac x=W' in exI)	
      apply (rule_tac x="(x#ys)" in exI)	
      apply (rule_tac x=zs in exI)	
      apply (simp add: Prog\<^sub>s\<^sub>b )
      done
    qed
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      nvo': "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and
      a_nro: "a \<notin> read_only \<S>" and
      a_unowned: "a \<notin> \<O>" and
      A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and
      R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and 
      a_unforw: "a \<in> unforwarded_non_volatile_reads sb X"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)

    show ?thesis
    proof (cases "a \<in> A")
      case True
      then show ?thesis
        apply -
	apply (rule disjI2)
	apply (rule_tac x=A in exI)
	apply (rule_tac x=L in exI)	
	apply (rule_tac x=R in exI)
	apply (rule_tac x=W in exI)
	apply (rule_tac x="[]" in exI)	
	apply (rule_tac x=sb in exI)	
	apply (simp add: Ghost\<^sub>s\<^sub>b True)
	done
    next
      case False

      with a_unowned a_nro L_A R_owns a_nro L_A A_R
      obtain a_nro': "a \<notin> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and a_unowned': "a \<notin> \<O> \<union> A - R"
	by (force simp add: in_read_only_convs)
      from Cons.hyps [OF nvo' consis' a_nro' a_unowned' a_unforw]
      have "(\<exists>sop a' v ys zs A L R W.
                 sb = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W # zs \<and>
                 a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys \<and> a' \<noteq> a) \<or>
              (\<exists>A L R W ys zs. sb = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys)"
        (is "?write \<or> ?ghst")
	by simp
      then show ?thesis
      proof 
	assume ?write

	then obtain sop' a'' v' ys zs A' L' R' W' where 
          sb: "sb = ys @ Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs" and
          props: "a \<in> A'" "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys \<and> a'' \<noteq> a"
	  by auto
	  
	  
	show ?thesis
	using props sb
	  apply -
	  apply (rule disjI1)
	  apply (rule_tac x=sop' in exI)
	  apply (rule_tac x=a'' in exI)	
	  apply (rule_tac x=v' in exI)	
	  apply (rule_tac x="(x#ys)" in exI)	
	  apply (rule_tac x=zs in exI)	
	  apply (simp add: Ghost\<^sub>s\<^sub>b False )
	  done
      next
	assume ?ghst
	then obtain ys zs A' L' R' W'  where 
          sb: "sb = ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs" and
          props: "a \<in> A'" "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys"
	  by auto
	  
	  
	show ?thesis
	using props sb
	  apply -
	  apply (rule disjI2)
	  apply (rule_tac x=A' in exI)
	  apply (rule_tac x=L' in exI)	
	  apply (rule_tac x=R' in exI)
	  apply (rule_tac x=W' in exI)	
	  apply (rule_tac x="(x#ys)" in exI)	
	  apply (rule_tac x=zs in exI)	
	  apply (simp add: Ghost\<^sub>s\<^sub>b False )
	  done
	qed
      qed
    qed
  qed (* FIXME: indentation*)

(*
lemma release_take_drop:
"\<And>\<R> S. release (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S (release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S \<R>) =
           release sb S \<R>"
apply (induct sb)
apply clarsimp
apply (auto split:memref.splits)
apply fastforce*)

lemma release_shared_exchange_weak: 
assumes shared_eq: "\<forall>a \<in> \<O> \<union> all_acquired sb. (\<S>'::shared) a = \<S> a"
assumes consis: "weak_sharing_consistent \<O> sb" 
shows "release sb (dom \<S>') \<R> = release sb (dom \<S>) \<R>"
using shared_eq consis 
proof (induct sb arbitrary: \<S> \<S>' \<O> \<R>)
  case Nil thus ?case by auto
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True

      from Cons.prems obtain 
	L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "weak_sharing_consistent (\<O> \<union> A - R) sb" and
        shared_eq: "\<forall>a \<in> \<O> \<union> A \<union> all_acquired sb. \<S>' a = \<S> a"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True )
      from shared_eq
      have shared_eq': "\<forall>a\<in>\<O> \<union> A - R \<union> all_acquired sb. (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
        by (auto simp add: augment_shared_def restrict_shared_def)
      from Cons.hyps [OF shared_eq' consis']
      have "release sb (dom (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) Map.empty = release sb (dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) Map.empty" .
      then show ?thesis
        by (auto  simp add: Write\<^sub>s\<^sub>b True domIff) 
    next
      case False with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W) 
    from Cons.prems obtain 
      L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "weak_sharing_consistent (\<O> \<union> A - R) sb" and
      shared_eq: "\<forall>a \<in> \<O> \<union> A \<union> all_acquired sb. \<S>' a = \<S> a"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b )
    from shared_eq
    have shared_eq': "\<forall>a\<in>\<O> \<union> A - R \<union> all_acquired sb. (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
      by (auto simp add: augment_shared_def restrict_shared_def)
    from shared_eq R_owns have "\<forall>a\<in>R. (a \<in> dom \<S>) = (a \<in> dom \<S>')"
      by (auto simp add: domIff)
    from augment_rels_shared_exchange [OF this]
    have "(augment_rels (dom \<S>') R \<R>) = (augment_rels (dom \<S>) R \<R>)".
    
    with Cons.hyps [OF shared_eq' consis']
    have "release sb (dom (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) (augment_rels (dom \<S>') R \<R>) = 
            release sb (dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) (augment_rels (dom \<S>) R \<R>)" by simp
    then show ?thesis
      by (clarsimp  simp add: Ghost\<^sub>s\<^sub>b domIff) 
  qed
qed


lemma read_only_share_all_shared: "\<And>\<S>. \<lbrakk> a \<in> read_only (share sb \<S>)\<rbrakk>
\<Longrightarrow> a \<in> read_only \<S> \<union> all_shared sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      with Write\<^sub>s\<^sub>b Cons.hyps [of "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"] Cons.prems
      show ?thesis
        by (auto simp add: read_only_def augment_shared_def restrict_shared_def 
          split: if_split_asm option.splits)
    next
      case False with Write\<^sub>s\<^sub>b Cons show ?thesis by auto
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    with Cons.hyps [of "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"] Cons.prems
    show ?thesis
      by (auto simp add: read_only_def augment_shared_def restrict_shared_def 
          split: if_split_asm option.splits)
  qed
qed

lemma read_only_shared_all_until_volatile_write_subset':
"\<And>\<S>. 
read_only (share_all_until_volatile_write ts \<S>) \<subseteq> 
  read_only \<S> \<union> (\<Union>((\<lambda>(_, _, _, sb, _, _ ,_). all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts))"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  obtain p "is" \<O> \<R> \<D> \<theta> sb where
    t: "t = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
    by (cases t)


  have aargh: "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) = (\<lambda>a. \<not> is_volatile_Write\<^sub>s\<^sub>b a)"
    by (rule ext) auto


  let ?take_sb = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
  let ?drop_sb = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"


 
  {
    fix a
    assume a_in: "a \<in> read_only
              (share_all_until_volatile_write ts
                 (share ?take_sb \<S>))" and
    a_notin_shared: "a \<notin> read_only \<S>" and
    a_notin_rest: "a \<notin> (\<Union>((\<lambda>(_, _, _, sb, _, _ ,_). all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts))"
    have "a \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
    proof -
      from Cons.hyps [of "(share ?take_sb \<S>)"] a_in a_notin_rest
      have "a \<in> read_only (share ?take_sb \<S>)"
        by (auto simp add: aargh)
      from read_only_share_all_shared [OF this] a_notin_shared
      show ?thesis by auto
    qed
  }
      
  then show ?case
    by (auto simp add: t aargh)
qed


lemma read_only_share_acquired_all_shared: 
  "\<And>\<O> \<S>. weak_sharing_consistent \<O> sb \<Longrightarrow> \<O> \<inter> read_only \<S> = {} \<Longrightarrow>
  a \<in> read_only (share sb \<S>) \<Longrightarrow> a \<in> \<O> \<union> all_acquired sb \<Longrightarrow> a \<in> all_shared sb"
proof (induct sb)
  case Nil thus ?case by auto
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain
	owns_ro: "\<O> \<inter> read_only \<S> = {}" and L_A: " L \<subseteq> A" and A_R: "A \<inter> R = {}" and
	R_owns: "R \<subseteq> \<O>" and consis': "weak_sharing_consistent  (\<O> \<union> A - R)  sb" and 
        a_share: "a \<in> read_only (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" and
        a_A_all: "a \<in> \<O> \<union> A \<union> all_acquired sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)

      from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
        by (auto simp add: in_read_only_convs)
      from Cons.hyps [OF consis' owns_ro' a_share]
      show ?thesis
      using L_A A_R R_owns owns_ro  a_A_all 
        by (auto simp add: Write\<^sub>s\<^sub>b volatile augment_shared_def restrict_shared_def read_only_def domIff
           split: if_split_asm)
    next 
      case False
      with Cons Write\<^sub>s\<^sub>b show ?thesis by (auto)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain
      owns_ro: "\<O> \<inter> read_only \<S> = {}" and L_A: " L \<subseteq> A" and A_R: "A \<inter> R = {}" and
      R_owns: "R \<subseteq> \<O>" and consis': "weak_sharing_consistent (\<O> \<union> A - R)  sb" and 
      a_share: "a \<in> read_only (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" and
      a_A_all: "a \<in> \<O> \<union> A \<union> all_acquired sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)

    from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
      by (auto simp add: in_read_only_convs)
    from Cons.hyps [OF consis' owns_ro' a_share]
    show ?thesis
    using L_A A_R R_owns owns_ro a_A_all 
      by (auto simp add: Ghost\<^sub>s\<^sub>b augment_shared_def restrict_shared_def read_only_def domIff
         split: if_split_asm)
  qed
qed

lemma read_only_share_unowned': "\<And>\<O> \<S>.
  \<lbrakk>weak_sharing_consistent \<O> sb; \<O> \<inter> read_only \<S> = {}; a \<notin> \<O> \<union> all_acquired sb; a \<in> read_only \<S>\<rbrakk> 
  \<Longrightarrow> a \<in> read_only (share sb \<S>)"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case False
      with Cons Write\<^sub>s\<^sub>b show ?thesis by auto
    next
      case True
      from Cons.prems obtain
	owns_ro: "\<O> \<inter> read_only \<S> = {}" and L_A: " L \<subseteq> A" and A_R: "A \<inter> R = {}" and
	R_owns: "R \<subseteq> \<O>" and consis': "weak_sharing_consistent  (\<O> \<union> A - R)  sb" and 
        a_share: "a \<in> read_only \<S>" and
        a_notin: "a \<notin> \<O>" "a \<notin> A" "a \<notin> all_acquired sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
        by (auto simp add: in_read_only_convs)
      from a_notin have a_notin': "a \<notin> \<O> \<union> A - R \<union> all_acquired sb"
         by auto
       from a_share  a_notin L_A A_R R_owns  have a_ro': "a \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
         by (auto simp add: read_only_def restrict_shared_def augment_shared_def)
       from Cons.hyps [OF consis' owns_ro' a_notin' a_ro']
       have "a \<in> read_only (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
         by auto
       then show ?thesis
         by (auto simp add: Write\<^sub>s\<^sub>b True)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain
      owns_ro: "\<O> \<inter> read_only \<S> = {}" and L_A: " L \<subseteq> A" and A_R: "A \<inter> R = {}" and
      R_owns: "R \<subseteq> \<O>" and consis': "weak_sharing_consistent  (\<O> \<union> A - R)  sb" and 
      a_share: "a \<in> read_only \<S>" and
      a_notin: "a \<notin> \<O>" "a \<notin> A" "a \<notin> all_acquired sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
      by (auto simp add: in_read_only_convs)
    from a_notin have a_notin': "a \<notin> \<O> \<union> A - R \<union> all_acquired sb"
      by auto
    from a_share  a_notin L_A A_R R_owns  have a_ro': "a \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
      by (auto simp add: read_only_def restrict_shared_def augment_shared_def)
    from Cons.hyps [OF consis' owns_ro' a_notin' a_ro']
    have "a \<in> read_only (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
      by auto
    then show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

(*
lemma release_False_mono:
  "\<And>S \<R>. \<R> a = Some False \<Longrightarrow> release sb S \<R> a = Some False "
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Ghost\<^sub>s\<^sub>b A L R W)
    have rels_a: "\<R> a = Some False" by fact
    then have "(augment_rels S R \<R>) a = Some False"
      by (auto simp add: augment_rels_def)
    from Cons.hyps [where \<R> = "(augment_rels S R \<R>)", OF this]    
    show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  next
    case Write\<^sub>s\<^sub>b with Cons show ?thesis apply auto
  next 
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  qed
qed
*)


lemma release_False_mono:
  "\<And>S \<R>. \<R> a = Some False \<Longrightarrow> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {} \<Longrightarrow> 
  release sb S \<R> a = Some False "
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Ghost\<^sub>s\<^sub>b A L R W)
    have rels_a: "\<R> a = Some False" by fact
    then have "(augment_rels S R \<R>) a = Some False"
      by (auto simp add: augment_rels_def)
    from Cons.hyps [where \<R> = "(augment_rels S R \<R>)", OF this] Cons.prems
    show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  next
    case Write\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next 
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  qed
qed

lemma release_False_mono_take:
  "\<And>S \<R>. \<R> a = Some False \<Longrightarrow> release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S \<R> a = Some False "
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Ghost\<^sub>s\<^sub>b A L R W)
    have rels_a: "\<R> a = Some False" by fact
    then have "(augment_rels S R \<R>) a = Some False"
      by (auto simp add: augment_rels_def)
    from Cons.hyps [where \<R> = "(augment_rels S R \<R>)", OF this]    
    show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  next
    case Write\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next 
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  qed
qed


lemma shared_switch: 
  "\<And>\<S> \<O>. \<lbrakk>weak_sharing_consistent \<O> sb; read_only \<S> \<inter> \<O> = {}; 
    \<S> a \<noteq> Some False; share sb \<S> a = Some False\<rbrakk> 
  \<Longrightarrow> a \<in> \<O> \<union> all_acquired sb "
proof (induct sb)
  case Nil thus ?case by (auto simp add: read_only_def)
next
  case (Cons x sb)
  have aargh: "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) = (\<lambda>a. \<not> is_volatile_Write\<^sub>s\<^sub>b a)"
    by (rule ext) auto
  show ?case
  proof (cases x)
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      dist: "read_only \<S> \<inter> \<O> = {}" and
      share: "\<S> a \<noteq> Some False" and
      share': "share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = Some False" and
      L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "weak_sharing_consistent (\<O> \<union> A - R) sb" by (clarsimp simp add: Ghost\<^sub>s\<^sub>b aargh)
  
    from dist L_A A_R R_owns have dist':  "read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<inter> (\<O> \<union> A - R)= {}"
      by (auto simp add: in_read_only_convs)

    show ?thesis
    proof (cases "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = Some False")
      case False
      from Cons.hyps [OF consis' dist' this share']
      show ?thesis by (auto simp add: Ghost\<^sub>s\<^sub>b)
    next
      case True
      with share L_A A_R R_owns dist
      have "a \<in> \<O> \<union> A"
        by (cases "\<S> a")      
           (auto simp add: augment_shared_def restrict_shared_def read_only_def split: if_split_asm )
      thus ?thesis by (auto simp add: Ghost\<^sub>s\<^sub>b)
   qed
 next
   case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
   show ?thesis
   proof (cases volatile)
     case True
     note volatile=this
     from Cons.prems obtain 
       dist: "read_only \<S> \<inter> \<O> = {}" and
       share: "\<S> a \<noteq> Some False" and
       share': "share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = Some False" and
       L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
       consis': "weak_sharing_consistent (\<O> \<union> A - R) sb" by (clarsimp simp add: Write\<^sub>s\<^sub>b True aargh)
  
     from dist L_A A_R R_owns have dist':  "read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<inter> (\<O> \<union> A - R)= {}"
       by (auto simp add: in_read_only_convs)

     show ?thesis
     proof (cases "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = Some False")
       case False
       from Cons.hyps [OF consis' dist' this share']
       show ?thesis by (auto simp add: Write\<^sub>s\<^sub>b True)
     next
       case True
       with share L_A A_R R_owns dist
       have "a \<in> \<O> \<union> A"
         by (cases "\<S> a")      
           (auto simp add: augment_shared_def restrict_shared_def read_only_def split: if_split_asm )
       thus ?thesis by (auto simp add: Write\<^sub>s\<^sub>b volatile)
     qed 
   next
     case False
     with Cons show ?thesis by (auto simp add: Write\<^sub>s\<^sub>b)
   qed
 next
   case Read\<^sub>s\<^sub>b with Cons show ?thesis by (auto)
 next
   case Prog\<^sub>s\<^sub>b with Cons show ?thesis by (auto)
 qed
qed

lemma shared_switch_release_False: 
  "\<And>\<S> \<R>. \<lbrakk>
     outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {};
     a \<notin> dom \<S>; 
     a \<in> dom (share sb \<S>)\<rbrakk>
   \<Longrightarrow>
      release sb (dom \<S>) \<R> a =  Some False" 
proof (induct sb)
  case Nil thus ?case by (auto simp add: read_only_def)
next
  case (Cons x sb)
  have aargh: "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) = (\<lambda>a. \<not> is_volatile_Write\<^sub>s\<^sub>b a)"
    by (rule ext) auto
  show ?case
  proof (cases x)
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      a_notin: "a \<notin> dom \<S>" and
      share: "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" and
      out': "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b aargh)
  
    show ?thesis
    proof (cases "a \<in> R")
      case False
      with a_notin have "a \<notin> dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
        by auto
      from Cons.hyps [OF out' this share]
      show ?thesis
        by (auto simp add: Ghost\<^sub>s\<^sub>b)
    next
      case True
      with a_notin have "augment_rels (dom \<S>) R \<R> a = Some False"
        by (auto simp add: augment_rels_def split: option.splits)
      from release_False_mono [of "augment_rels (dom \<S>) R \<R>", OF this out'] 
      show ?thesis
        by (auto simp add: Ghost\<^sub>s\<^sub>b)
    qed
  next
    case Write\<^sub>s\<^sub>b with Cons show ?thesis by (clarsimp split: if_split_asm)
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next 
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  qed 
qed


lemma release_not_unshared_no_write:  
  "\<And>\<S> \<R>. \<lbrakk>
     outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {};     
  non_volatile_writes_unshared \<S> sb;
  release sb (dom \<S>) \<R> a \<noteq>  Some False;
  a \<in> dom (share sb \<S>)\<rbrakk>
   \<Longrightarrow>
    a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb" 
proof (induct sb)
  case Nil thus ?case by (auto simp add: read_only_def)
next
  case (Cons x sb)
  have aargh: "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) = (\<lambda>a. \<not> is_volatile_Write\<^sub>s\<^sub>b a)"
    by (rule ext) auto
  show ?case
  proof (cases x)
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      share: "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" and
      rel: "release sb 
                (dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) (augment_rels (dom \<S>) R \<R>) a \<noteq>  Some False" and
      out': "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}" and
      nvu: "non_volatile_writes_unshared (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) sb" 
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b )
  
    
    from Cons.hyps [OF out' nvu rel share]
    show ?thesis by (auto simp add: Ghost\<^sub>s\<^sub>b)
  next
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True with Write\<^sub>s\<^sub>b Cons.prems have False by auto
      thus ?thesis ..
    next
      case False
      note not_vol = this
      from Cons.prems obtain 
        rel: "release sb (dom \<S>) \<R> a \<noteq>  Some False" and
        out': "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}" and
        nvo: "non_volatile_writes_unshared \<S> sb" and
        a'_not_dom: "a' \<notin> dom \<S>" and
        a_dom: "a \<in> dom (share sb \<S>)"
        by (auto simp add: Write\<^sub>s\<^sub>b False)
      from Cons.hyps [OF out' nvo rel a_dom]
      have a_notin_rest: "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb".
      
      show ?thesis
      proof (cases "a'=a")
        case False with a_notin_rest
        show ?thesis by (clarsimp simp add: Write\<^sub>s\<^sub>b  not_vol )
      next
        case True
        from shared_switch_release_False [OF out' a'_not_dom [simplified True] a_dom]
        have "release sb (dom \<S>) \<R> a =  Some False".
        with rel have False by simp
        thus ?thesis ..
      qed
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next 
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  qed 
qed

corollary release_not_unshared_no_write_take:  
 assumes nvw: "non_volatile_writes_unshared \<S> (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
 assumes rel: "release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) (dom \<S>) \<R> a \<noteq>  Some False"
 assumes a_in: "a \<in> dom (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>)"
 shows
    "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)" 
using release_not_unshared_no_write[OF takeWhile_not_vol_write_outstanding_refs [of sb] nvw rel a_in]
by simp

(* FIXME: may replace the un-primed variants, similar for the following lemmas *)
lemma read_only_unacquired_share':
  "\<And>S \<O>. \<lbrakk>\<O> \<inter> read_only S = {}; weak_sharing_consistent \<O> sb; a \<in> read_only S; 
  a \<notin> all_shared sb; a \<notin> acquired True sb \<O> \<rbrakk>
\<Longrightarrow> a \<in> read_only (share sb S)"
proof (induct sb)
    case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems
      obtain a_ro: "a \<in> read_only S" and a_R: "a \<notin> R" and a_unsh: "a \<notin> all_shared sb" and 
	owns_ro: "\<O> \<inter> read_only S = {}" and 
	L_A: "L \<subseteq> A" and A_R:  "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "weak_sharing_consistent (\<O> \<union> A - R) sb" and
        a_notin: "a \<notin> acquired True sb (\<O> \<union> A - R)" 
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      show ?thesis
      proof (cases "a \<in> A")
        case True
        with a_R have "a \<in> \<O> \<union> A - R" by auto
        from all_shared_acquired_in [OF this a_unsh]
        have "a \<in>  acquired True sb (\<O> \<union> A - R)" by auto
        with a_notin have False by auto
        thus ?thesis ..
      next
        case False
        
        from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	  by (auto simp add: in_read_only_convs)

        from a_ro False owns_ro R_owns L_A have a_ro': "a \<in> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	  by (auto simp add: in_read_only_convs)
        from Cons.hyps [OF owns_ro' consis' a_ro' a_unsh a_notin]
        show ?thesis
	  by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      qed
   next
      case False
      with Cons show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by (clarsimp)
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by (clarsimp)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems
    obtain a_ro: "a \<in> read_only S" and a_R: "a \<notin> R" and a_unsh: "a \<notin> all_shared sb" and 
      owns_ro: "\<O> \<inter> read_only S = {}" and 
      L_A: "L \<subseteq> A" and A_R:  "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "weak_sharing_consistent (\<O> \<union> A - R) sb" and
      a_notin: "a \<notin> acquired True sb (\<O> \<union> A - R)" 
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    show ?thesis
    proof (cases "a \<in> A")
      case True
      with a_R have "a \<in> \<O> \<union> A - R" by auto
      from all_shared_acquired_in [OF this a_unsh]
      have "a \<in>  acquired True sb (\<O> \<union> A - R)" by auto
      with a_notin have False by auto
      thus ?thesis ..
    next
      case False
      
      from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
        by (auto simp add: in_read_only_convs)

      from a_ro False owns_ro R_owns L_A have a_ro': "a \<in> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
        by (auto simp add: in_read_only_convs)
      from Cons.hyps [OF owns_ro' consis' a_ro' a_unsh a_notin]
      show ?thesis
        by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    qed
  qed
qed

lemma read_only_share_all_until_volatile_write_unacquired':
  "\<And>\<S>. \<lbrakk>ownership_distinct ts; read_only_unowned \<S> ts; weak_sharing_consis ts; 
  \<forall>i < length ts. (let (_,_,_,sb,_,\<O>,\<R>) = ts!i in 
            a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O> \<and>
            a \<notin> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb
     )); 
  a \<in> read_only \<S>\<rbrakk> 
  \<Longrightarrow> a \<in> read_only (share_all_until_volatile_write ts \<S>)"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  obtain p "is" \<O> \<R> \<D> \<theta> sb where
    t: "t = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
    by (cases t)

  have dist: "ownership_distinct (t#ts)" by fact
  then interpret ownership_distinct "t#ts" .
  from ownership_distinct_tl [OF dist]
  have dist': "ownership_distinct ts".


  have aargh: "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) = (\<lambda>a. \<not> is_volatile_Write\<^sub>s\<^sub>b a)"
    by (rule ext) auto

  have a_ro: "a \<in> read_only \<S>" by fact
  have ro_unowned: "read_only_unowned \<S> (t#ts)" by fact
  then interpret read_only_unowned \<S> "t#ts" .
  have consis: "weak_sharing_consis (t#ts)" by fact
  then interpret weak_sharing_consis "t#ts" .

  note consis' = weak_sharing_consis_tl [OF consis]

  let ?take_sb = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
  let ?drop_sb = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"

  from weak_sharing_consis [of 0] t
  have consis_sb: "weak_sharing_consistent \<O> sb"
    by force
  with weak_sharing_consistent_append [of \<O> ?take_sb ?drop_sb]
  have consis_take: "weak_sharing_consistent \<O> ?take_sb"
    by auto


  have ro_unowned': "read_only_unowned (share ?take_sb \<S>) ts"
  proof 
    fix j
    fix p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j
    assume j_bound: "j < length ts"
    assume jth: "ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
    show "\<O>\<^sub>j \<inter> read_only (share ?take_sb \<S>) = {}"
    proof -
      {
        fix a
        assume a_owns: "a \<in> \<O>\<^sub>j" 
        assume a_ro: "a \<in> read_only (share ?take_sb \<S>)"
        have False
        proof -
          from ownership_distinct [of 0 "Suc j"] j_bound jth t
          have dist: "(\<O> \<union> all_acquired sb) \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {}"
            by fastforce
    
          from read_only_unowned [of "Suc j"] j_bound jth
          have dist_ro: "\<O>\<^sub>j \<inter> read_only \<S> = {}" by force
          show ?thesis
          proof (cases "a \<in> (\<O> \<union> all_acquired sb)")
            case True
            with dist a_owns show False by auto
          next
            case False
            hence "a \<notin>  (\<O> \<union> all_acquired ?take_sb)"
            using all_acquired_append [of ?take_sb ?drop_sb]
              by auto
            from read_only_share_unowned [OF consis_take this a_ro]
            have "a \<in> read_only \<S>".
            with dist_ro a_owns show False by auto
         qed
       qed
      }
      thus ?thesis by auto
    qed
  qed

      
  from Cons.prems
  obtain unacq_ts: "\<forall>i < length ts. (let (_,_,_,sb,_,\<O>,_) = ts!i in 
           a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O> \<and>
            a \<notin> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) " and
    unacq_sb: "a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>" and
    unsh_sb: "a \<notin> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) "

   apply clarsimp
   apply (rule that)
   apply (auto simp add: t aargh)
   done

  
  from read_only_unowned [of 0] t
  have owns_ro: "\<O> \<inter> read_only \<S> = {}"
    by force


  from read_only_unacquired_share' [OF owns_ro consis_take a_ro unsh_sb unacq_sb]
  have "a \<in> read_only (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>)".
  from Cons.hyps [OF dist' ro_unowned' consis' unacq_ts this]
  show ?case
    by (simp add: t)
qed


  

lemma not_shared_not_acquired_switch:
  "\<And>X Y. \<lbrakk>a \<notin> all_shared sb; a \<notin> X; a \<notin> acquired True sb X; a \<notin> Y\<rbrakk>  \<Longrightarrow> a \<notin> acquired True sb Y"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      from Cons.prems obtain 
        a_X: "a \<notin> X"  and a_acq: "a \<notin> acquired True sb (X \<union> A - R)" and 
        a_Y: "a \<notin> Y" and a_R: "a \<notin> R" and 
        a_shared: "a \<notin> all_shared sb"
        by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      show ?thesis
      proof (cases "a \<in> A")
        case True
        with a_X a_R 
        have "a \<in> X \<union> A - R" by auto
        from all_shared_acquired_in [OF this a_shared]
        have "a \<in> acquired True sb (X \<union> A - R)".
        with a_acq have False by simp 
        thus ?thesis ..
     next
       case False
       with a_X a_Y obtain a_X': "a \<notin> X \<union> A - R" and a_Y': "a \<notin> Y \<union> A - R"
         by auto
       from Cons.hyps [OF a_shared a_X' a_acq a_Y']
       show ?thesis
         by (auto simp add: Write\<^sub>s\<^sub>b True)
     qed
   next
     case False with Cons.hyps [of X Y] Cons.prems show ?thesis by (auto simp add: Write\<^sub>s\<^sub>b)
   qed
 next
   case Read\<^sub>s\<^sub>b with Cons.hyps [of X Y] Cons.prems show ?thesis by (auto)
 next
   case Prog\<^sub>s\<^sub>b with Cons.hyps [of X Y] Cons.prems show ?thesis by (auto)
 next
   case (Ghost\<^sub>s\<^sub>b A L R W)
   from Cons.prems obtain 
     a_X: "a \<notin> X"  and a_acq: "a \<notin> acquired True sb (X \<union> A - R)" and 
     a_Y: "a \<notin> Y" and a_R: "a \<notin> R" and 
     a_shared: "a \<notin> all_shared sb"
     by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
   show ?thesis
   proof (cases "a \<in> A")
     case True
     with a_X a_R 
     have "a \<in> X \<union> A - R" by auto
     from all_shared_acquired_in [OF this a_shared]
     have "a \<in> acquired True sb (X \<union> A - R)".
     with a_acq have False by simp 
     thus ?thesis ..
   next
     case False
     with a_X a_Y obtain a_X': "a \<notin> X \<union> A - R" and a_Y': "a \<notin> Y \<union> A - R"
       by auto
     from Cons.hyps [OF a_shared a_X' a_acq a_Y']
     show ?thesis
       by (auto simp add: Ghost\<^sub>s\<^sub>b)
   qed
 qed
qed

(* FIXME: could be strengthened to acquired True sb empty I suppose *)
lemma read_only_share_all_acquired_in': 
  "\<And>S \<O>. \<lbrakk>\<O> \<inter> read_only S = {}; weak_sharing_consistent \<O> sb; a \<in> read_only (share sb S)\<rbrakk> 
  \<Longrightarrow> a \<in> read_only (share sb Map.empty) \<or> (a \<in> read_only S \<and> a \<notin> acquired True sb \<O> \<and> a \<notin> all_shared sb )"
proof (induct sb)
    case Nil thus ?case by auto
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems
      obtain a_in: "a \<in> read_only (share sb (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" and
	owns_ro: "\<O> \<inter> read_only S = {}" and 
	L_A: "L \<subseteq> A" and A_R:  "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "weak_sharing_consistent (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)

      from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	by (auto simp add: in_read_only_convs)

      from Cons.hyps [OF owns_ro' consis' a_in]
      have hyp: "a \<in> read_only (share sb Map.empty) \<or> 
                 (a \<in> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<and> a \<notin> acquired True sb (\<O> \<union> A - R) \<and> a \<notin> all_shared sb)".

      have "a \<in> read_only (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) \<or> 
           (a \<in> read_only S \<and> a \<notin> R \<and> a \<notin> acquired True sb (\<O> \<union> A - R) \<and> a \<notin> all_shared sb)"
      proof -
	{
	  assume a_emp: "a \<in> read_only (share sb Map.empty)"
	  have "read_only Map.empty \<subseteq> read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	    by (auto simp add: in_read_only_convs)
	  
	  from share_read_only_mono_in [OF a_emp this]
	  have "a \<in> read_only (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))".
	}
	moreover
	{
	  assume a_ro: "a \<in> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and
            a_not_acq: "a \<notin> acquired True sb (\<O> \<union> A - R)" and  
            a_unsh: "a \<notin> all_shared sb" 
          have ?thesis
	  proof (cases "a \<in> read_only S")
	    case True
	    with a_ro obtain a_A: "a \<notin> A"
	      by (auto simp add: in_read_only_convs)
            with True a_not_acq a_unsh R_owns owns_ro
            show ?thesis
               by auto
          next
            case False
	    with a_ro have a_ro_empty: "a \<in> read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	      by (auto simp add: in_read_only_convs split: if_split_asm)
	    
	    have "read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<subseteq> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	      by (auto simp add: in_read_only_convs)
	    with owns_ro'
	    have owns_ro_empty: "(\<O> \<union> A - R) \<inter> read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	      by blast


	    from read_only_unacquired_share' [OF owns_ro_empty consis' a_ro_empty a_unsh a_not_acq]
	    have "a \<in> read_only (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))".
	    thus ?thesis
	      by simp
	  qed
	}
	moreover note hyp
	ultimately show ?thesis by blast
      qed

      then show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
    next
      case False with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems
    obtain a_in: "a \<in> read_only (share sb (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" and
      owns_ro: "\<O> \<inter> read_only S = {}" and 
      L_A: "L \<subseteq> A" and A_R:  "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "weak_sharing_consistent (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    
    from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
      by (auto simp add: in_read_only_convs)

    from Cons.hyps [OF owns_ro' consis' a_in]
    have hyp: "a \<in> read_only (share sb Map.empty) \<or> 
                 (a \<in> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<and> a \<notin> acquired True sb (\<O> \<union> A - R) \<and> a \<notin> all_shared sb)".

    have "a \<in> read_only (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) \<or> 
           (a \<in> read_only S \<and> a \<notin> R \<and> a \<notin> acquired True sb (\<O> \<union> A - R) \<and> a \<notin> all_shared sb)"
    proof -
      {
	assume a_emp: "a \<in> read_only (share sb Map.empty)"
	have "read_only Map.empty \<subseteq> read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	  by (auto simp add: in_read_only_convs)
	  
	from share_read_only_mono_in [OF a_emp this]
	have "a \<in> read_only (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))".
      }
      moreover
      {
	assume a_ro: "a \<in> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and
          a_not_acq: "a \<notin> acquired True sb (\<O> \<union> A - R)" and  
          a_unsh: "a \<notin> all_shared sb" 
        have ?thesis
        proof (cases "a \<in> read_only S")
	  case True
	  with a_ro obtain a_A: "a \<notin> A"
	    by (auto simp add: in_read_only_convs)
          with True a_not_acq a_unsh R_owns owns_ro
          show ?thesis
            by auto
        next
          case False
	  with a_ro have a_ro_empty: "a \<in> read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	    by (auto simp add: in_read_only_convs split: if_split_asm)
	    
	  have "read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<subseteq> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	    by (auto simp add: in_read_only_convs)
	  with owns_ro'
	  have owns_ro_empty: "(\<O> \<union> A - R) \<inter> read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	    by blast


	  from read_only_unacquired_share' [OF owns_ro_empty consis' a_ro_empty a_unsh a_not_acq]
	  have "a \<in> read_only (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))".
	  thus ?thesis
	    by simp
	qed
      }
      moreover note hyp
      ultimately show ?thesis by blast
    qed
    
    then show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

lemma in_read_only_share_all_until_volatile_write':
  assumes dist: "ownership_distinct ts"
  assumes consis: "sharing_consis \<S> ts"
  assumes ro_unowned: "read_only_unowned \<S> ts"
  assumes i_bound: "i < length ts"
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
  assumes a_unacquired_others: "\<forall>j < length ts. i\<noteq>j \<longrightarrow> 
            (let (_,_,_,sb\<^sub>j,_,\<O>,_) = ts!j in
            a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O> \<and>
            a \<notin> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j ))"
  assumes a_ro_share: "a \<in> read_only (share sb \<S>)"
  shows "a \<in> read_only (share (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) 
                    (share_all_until_volatile_write ts \<S>))"
proof -
  from consis
  interpret sharing_consis \<S> ts .
  interpret read_only_unowned \<S> ts by fact

  from sharing_consis [OF i_bound ts_i]
  have consis_sb: "sharing_consistent \<S> \<O> sb".
  from sharing_consistent_weak_sharing_consistent [OF this] 
  have weak_consis: "weak_sharing_consistent \<O> sb".
  from read_only_unowned [OF i_bound ts_i]
  have owns_ro: "\<O> \<inter> read_only \<S> = {}".
  from read_only_share_all_acquired_in' [OF owns_ro weak_consis a_ro_share]
  (* make similar version with acquired and all_shared instead of all_acquired *)
  have "a \<in> read_only (share sb Map.empty) \<or> a \<in> read_only \<S> \<and> a \<notin> acquired True sb \<O> \<and> a \<notin> all_shared sb".
  moreover
  
  let ?take_sb = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
  let ?drop_sb = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"

  from weak_consis weak_sharing_consistent_append [of \<O> ?take_sb ?drop_sb]
  obtain weak_consis': "weak_sharing_consistent (acquired True ?take_sb \<O>) ?drop_sb" and
    weak_consis_take: "weak_sharing_consistent \<O> ?take_sb" 
    by auto
  
  {
    assume "a \<in> read_only (share sb Map.empty)"
    with share_append [of ?take_sb ?drop_sb]
    have a_in': "a \<in> read_only (share ?drop_sb (share ?take_sb Map.empty))"
      by auto

    have owns_empty: "\<O> \<inter> read_only Map.empty = {}"
      by auto

    from weak_sharing_consistent_preserves_distinct [OF weak_consis_take owns_empty]
    have "acquired True ?take_sb \<O> \<inter> read_only (share ?take_sb Map.empty) = {}".

    from read_only_share_all_acquired_in [OF this weak_consis' a_in']
    have "a \<in> read_only (share ?drop_sb Map.empty) \<or> a \<in> read_only (share ?take_sb Map.empty) \<and> a \<notin> all_acquired ?drop_sb".
    moreover
    {
      assume a_ro_drop: "a \<in> read_only (share ?drop_sb Map.empty)"
      have "read_only Map.empty \<subseteq> read_only (share_all_until_volatile_write ts \<S>)"
	by auto
      from share_read_only_mono_in [OF a_ro_drop this]
      have ?thesis .
    }
    moreover
    {
      assume a_ro_take: "a \<in> read_only (share ?take_sb Map.empty)" 
      assume a_unacq_drop: "a \<notin> all_acquired ?drop_sb"
      from read_only_share_unowned_in [OF weak_consis_take a_ro_take] 
      have "a \<in> \<O> \<union> all_acquired ?take_sb" by auto
      hence "a \<in> \<O> \<union> all_acquired sb" using all_acquired_append [of ?take_sb ?drop_sb]
        by auto
      from  share_all_until_volatile_write_thread_local' [OF dist consis i_bound ts_i this] a_ro_share
      have ?thesis by (auto simp add: read_only_def)
    }
    ultimately have ?thesis by blast
  }

  moreover

  {
    assume a_ro: "a \<in> read_only \<S>" 
    assume a_unacq: "a \<notin> acquired True sb \<O>"
    assume a_unsh: "a \<notin> all_shared sb"
    with all_shared_append [of ?take_sb ?drop_sb]
    obtain a_notin_take: "a \<notin> all_shared ?take_sb" and a_notin_drop: "a \<notin> all_shared ?drop_sb"
      by auto
    have ?thesis
    proof (cases "a \<in> acquired True ?take_sb \<O>")
      case True
      from all_shared_acquired_in [OF this a_notin_drop] acquired_append [of True ?take_sb ?drop_sb \<O>] a_unacq
      have False
        by auto
      thus ?thesis ..
    next
      case False
      with a_unacquired_others i_bound ts_i a_notin_take
      have a_unacq': "\<forall>j < length ts.  
            (let (_,_,_,sb\<^sub>j,_,\<O>,_) = ts!j in
            a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O> \<and>
            a \<notin> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j ))"
        by (auto simp add: Let_def)

      from local.weak_sharing_consis_axioms have "weak_sharing_consis ts" .
      from read_only_share_all_until_volatile_write_unacquired' [OF dist ro_unowned 
       \<open>weak_sharing_consis ts\<close> a_unacq' a_ro] 
      have a_ro_all: "a \<in> read_only (share_all_until_volatile_write ts \<S>)" .

      from weak_consis weak_sharing_consistent_append [of \<O> ?take_sb ?drop_sb]
      have weak_consis_drop: "weak_sharing_consistent (acquired True ?take_sb \<O>) ?drop_sb"
        by auto

      from weak_sharing_consistent_preserves_distinct_share_all_until_volatile_write [OF dist 
        ro_unowned \<open>weak_sharing_consis ts\<close> i_bound ts_i]
      have "acquired True ?take_sb \<O> \<inter>
         read_only (share_all_until_volatile_write ts \<S>) = {}".

      from read_only_unacquired_share' [OF this weak_consis_drop a_ro_all a_notin_drop]
        acquired_append [of True ?take_sb ?drop_sb \<O>] a_unacq
      show ?thesis by auto
    qed
  }
  ultimately show ?thesis by blast
qed

lemma all_acquired_unshared_acquired:
  "\<And>\<O>. a \<in> all_acquired sb ==> a \<notin> all_shared sb ==> a \<in> acquired True sb \<O>"
apply (induct sb)
apply (auto split: memref.split intro: all_shared_acquired_in)
done




lemma  safe_RMW_common:
  assumes safe: "\<O>s,\<R>s,i\<turnstile> (RMW a t (D,f) cond ret A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"
  shows "(a \<in> \<O> \<or> a \<in> dom \<S>) \<and> (\<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> (\<R>s!j) a \<noteq> Some False)"
using safe 
apply (cases)
apply (auto simp add: domIff)
done


lemma acquired_reads_all_acquired': "\<And>\<O>.
  acquired_reads True sb \<O> \<subseteq> acquired True sb \<O> \<union> all_shared sb"
apply (induct sb)
apply  clarsimp
apply (auto split: memref.splits dest: all_shared_acquired_in)
done


lemma release_all_shared_exchange: 
  "\<And>\<R> S' S. \<forall>a \<in> all_shared sb. (a \<in> S') = (a \<in> S) \<Longrightarrow> release sb S' \<R> = release sb S \<R>"
proof (induct sb)
  case Nil thus ?case by auto
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.hyps [of "(S' \<union> R - L)" "(S \<union> R - L)" Map.empty] Cons.prems
      show ?thesis
        by (auto simp add: Write\<^sub>s\<^sub>b volatile)
    next
      case False with Cons Write\<^sub>s\<^sub>b show ?thesis by auto
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)  
    from augment_rels_shared_exchange [of R S S' \<R>] Cons.prems
    have "augment_rels S' R \<R> = augment_rels S R \<R>"
      by (auto simp add: Ghost\<^sub>s\<^sub>b)

    with Cons.hyps [of "(S' \<union> R - L)" "(S \<union> R - L)" "augment_rels S R \<R>"] Cons.prems
    show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

lemma release_append_Prog\<^sub>s\<^sub>b:
"\<And>S \<R>. (release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis])) S \<R>) = 
       (release  (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S \<R>) "
  by (induct sb) (auto split: memref.splits)

subsection \<open>Simulation of Store Buffer Machine with History by Virtual Machine with Delayed Releases\<close>

theorem (in xvalid_program) concurrent_direct_steps_simulates_store_buffer_history_step:
  assumes step_sb: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h (ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b')"
  assumes valid_own: "valid_ownership \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b"
  assumes valid_sb_reads: "valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b"
  assumes valid_hist: "valid_history program_step ts\<^sub>s\<^sub>b"
  assumes valid_sharing: "valid_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b"
  assumes tmps_distinct: "tmps_distinct ts\<^sub>s\<^sub>b"
  assumes valid_sops: "valid_sops ts\<^sub>s\<^sub>b"
  assumes valid_dd: "valid_data_dependency ts\<^sub>s\<^sub>b"
  assumes load_tmps_fresh: "load_tmps_fresh ts\<^sub>s\<^sub>b"
  assumes enough_flushs: "enough_flushs ts\<^sub>s\<^sub>b"
  assumes valid_program_history: "valid_program_history ts\<^sub>s\<^sub>b"
  assumes valid: "valid ts\<^sub>s\<^sub>b"
  assumes sim: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<sim> (ts,m,\<S>)"
  assumes safe_reach: "safe_reach_direct safe_delayed (ts,m,\<S>)"
  shows "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<and> valid_reads m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<and> valid_history program_step ts\<^sub>s\<^sub>b' \<and>
         valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<and> tmps_distinct ts\<^sub>s\<^sub>b' \<and> valid_data_dependency ts\<^sub>s\<^sub>b' \<and>
         valid_sops ts\<^sub>s\<^sub>b' \<and> load_tmps_fresh ts\<^sub>s\<^sub>b' \<and> enough_flushs ts\<^sub>s\<^sub>b' \<and>
         valid_program_history ts\<^sub>s\<^sub>b' \<and> valid ts\<^sub>s\<^sub>b' \<and>
           (\<exists>ts' \<S>' m'. (ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>') \<and> 
                     (ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b') \<sim> (ts',m',\<S>'))"
  
proof -

  interpret direct_computation:
    computation direct_memop_step empty_storebuffer_step program_step "\<lambda>p p' is sb. sb" .
  interpret sbh_computation: 
    computation sbh_memop_step flush_step program_step 
       "\<lambda>p p' is sb. sb @ [Prog\<^sub>s\<^sub>b p p' is]" .
  interpret valid_ownership \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b by fact
  interpret valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b by fact
  interpret valid_history program_step ts\<^sub>s\<^sub>b by fact
  interpret valid_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b by fact
  interpret tmps_distinct ts\<^sub>s\<^sub>b by fact
  interpret valid_sops ts\<^sub>s\<^sub>b by fact
  interpret valid_data_dependency ts\<^sub>s\<^sub>b by fact
  interpret load_tmps_fresh ts\<^sub>s\<^sub>b by fact
  interpret enough_flushs ts\<^sub>s\<^sub>b by fact
  interpret valid_program_history ts\<^sub>s\<^sub>b by fact
  from valid_own valid_sharing
  have valid_own_sharing: "valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b"
    by (simp add: valid_sharing_def valid_ownership_and_sharing_def)
  then
  interpret valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b .

  from safe_reach_safe_refl [OF safe_reach]
  have safe: "safe_delayed (ts,m,\<S>)".

  from step_sb
  show ?thesis
  proof (cases)
    case (Memop i p\<^sub>s\<^sub>b "is\<^sub>s\<^sub>b" \<theta>\<^sub>s\<^sub>b sb  \<D>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b \<R>\<^sub>s\<^sub>b  "is\<^sub>s\<^sub>b'" \<theta>\<^sub>s\<^sub>b' sb'  \<D>\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b')
    then obtain 
      ts\<^sub>s\<^sub>b': "ts\<^sub>s\<^sub>b' = ts\<^sub>s\<^sub>b[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b',\<theta>\<^sub>s\<^sub>b', sb', \<D>\<^sub>s\<^sub>b', \<O>\<^sub>s\<^sub>b',\<R>\<^sub>s\<^sub>b')]" and
      i_bound: "i < length ts\<^sub>s\<^sub>b" and
      ts\<^sub>s\<^sub>b_i: "ts\<^sub>s\<^sub>b ! i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b,\<theta>\<^sub>s\<^sub>b,sb, \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b)" and
      sbh_step: "(is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b, sb, m\<^sub>s\<^sub>b, \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b, \<R>\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h 
                  (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b', sb', m\<^sub>s\<^sub>b', \<D>\<^sub>s\<^sub>b', \<O>\<^sub>s\<^sub>b', \<R>\<^sub>s\<^sub>b', \<S>\<^sub>s\<^sub>b')"
      by auto

    from sim obtain 
      m: "m = flush_all_until_volatile_write ts\<^sub>s\<^sub>b m\<^sub>s\<^sub>b" and
      \<S>: "\<S> = share_all_until_volatile_write ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b" and
      leq: "length ts\<^sub>s\<^sub>b = length ts" and
      ts_sim: "\<forall>i<length ts\<^sub>s\<^sub>b.
           let (p, is\<^sub>s\<^sub>b, \<theta>, sb, \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b,\<R>) = ts\<^sub>s\<^sub>b ! i;
               suspends = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb
           in  \<exists>is \<D>. instrs suspends @ is\<^sub>s\<^sub>b = is @ prog_instrs suspends \<and>
                    \<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {}) \<and>
                    ts ! i =
                   (hd_prog p suspends, 
                    is,
                    \<theta> |` (dom \<theta> - read_tmps suspends), (),
                    \<D>, 
                    acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>\<^sub>s\<^sub>b,
                    release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) (dom \<S>\<^sub>s\<^sub>b) \<R>)"
      by cases blast

    from i_bound leq have i_bound': "i < length ts"
      by auto

    have split_sb: "sb = takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb @ dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb"
      (is "sb = ?take_sb@?drop_sb")
      by simp

    from ts_sim [rule_format, OF i_bound] ts\<^sub>s\<^sub>b_i obtain suspends "is" \<D> where
      suspends: "suspends = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb" and
      is_sim: "instrs suspends @ is\<^sub>s\<^sub>b = is @ prog_instrs suspends" and
      \<D>: "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {})" and
      ts_i: "ts ! i =
          (hd_prog p\<^sub>s\<^sub>b suspends, is,
           \<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b - read_tmps suspends), (), \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,
            release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
      by (auto simp add: Let_def)

    from sbh_step_preserves_valid [OF i_bound ts\<^sub>s\<^sub>b_i sbh_step valid]
    have valid': "valid ts\<^sub>s\<^sub>b'"
      by (simp add: ts\<^sub>s\<^sub>b')
    

    from \<D> have \<D>\<^sub>s\<^sub>b: "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ?drop_sb \<noteq> {})"
      apply -
      apply (case_tac "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}")
      apply  (fastforce simp add: outstanding_refs_conv dest: set_dropWhileD)
      apply (clarsimp)
      apply (drule outstanding_refs_non_empty_dropWhile)
      apply blast
      done

    let ?ts' = "ts[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b, (), \<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b,
                         release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)]"
    have i_bound_ts': "i < length ?ts'"
      using i_bound'
      by auto
    hence ts'_i: "?ts'!i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b, (), 
                     \<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b, release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
      by simp 

    from local.sharing_consis_axioms
    have sharing_consis_ts\<^sub>s\<^sub>b: "sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b" .
    from sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]
    have sharing_consis_sb: "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb".
    from sharing_consistent_weak_sharing_consistent [OF this]
    have weak_consis_sb: "weak_sharing_consistent \<O>\<^sub>s\<^sub>b sb".
    from this weak_sharing_consistent_append [of \<O>\<^sub>s\<^sub>b ?take_sb ?drop_sb]
    have weak_consis_drop:"weak_sharing_consistent (acquired True ?take_sb \<O>\<^sub>s\<^sub>b) ?drop_sb"
      by auto
    from local.ownership_distinct_axioms
    have ownership_distinct_ts\<^sub>s\<^sub>b: "ownership_distinct ts\<^sub>s\<^sub>b" .
    have steps_flush_sb: "(ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (?ts', flush ?drop_sb m, share ?drop_sb \<S>)"
    proof -
      from valid_reads [OF i_bound ts\<^sub>s\<^sub>b_i]
      have reads_consis: "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b sb".
      from reads_consistent_drop_volatile_writes_no_volatile_reads [OF this]
      have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b ?drop_sb = {}".
      from valid_program_history [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "causal_program_history is\<^sub>s\<^sub>b sb".
      then have cph: "causal_program_history is\<^sub>s\<^sub>b ?drop_sb"
	apply -
	apply (rule causal_program_history_suffix [where sb="?take_sb"] )
	apply (simp)
	done
      from valid_last_prog [OF i_bound ts\<^sub>s\<^sub>b_i] have last_prog: "last_prog p\<^sub>s\<^sub>b sb = p\<^sub>s\<^sub>b".
      then
      have lp: "last_prog p\<^sub>s\<^sub>b ?drop_sb = p\<^sub>s\<^sub>b"
	apply -
	apply (rule last_prog_same_append [where sb="?take_sb"])
	apply simp
	done

      from reads_consistent_flush_all_until_volatile_write [OF valid_own_sharing i_bound 
	ts\<^sub>s\<^sub>b_i reads_consis]
      have reads_consis_m: "reads_consistent True (acquired True ?take_sb \<O>\<^sub>s\<^sub>b) m ?drop_sb"
	by (simp add: m)
      
      from valid_history [OF i_bound ts\<^sub>s\<^sub>b_i]
      have h_consis: "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b (?take_sb@?drop_sb)) (?take_sb@?drop_sb)"
	by (simp)
      
      have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>s\<^sub>b sb) ?take_sb = (hd_prog p\<^sub>s\<^sub>b ?drop_sb)"
      proof -
	from last_prog_hd_prog_append' [OF h_consis] last_prog
	have "last_prog (hd_prog p\<^sub>s\<^sub>b ?drop_sb) ?take_sb = hd_prog p\<^sub>s\<^sub>b ?drop_sb"
	  by (simp)
	moreover 
	have "last_prog (hd_prog p\<^sub>s\<^sub>b (?take_sb @ ?drop_sb)) ?take_sb = 
          last_prog (hd_prog p\<^sub>s\<^sub>b ?drop_sb) ?take_sb"
	  by (rule last_prog_hd_prog_append)
	ultimately show ?thesis
	  by (simp)
      qed
       
      from valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "\<forall>sop\<in>write_sops (?take_sb@?drop_sb). valid_sop sop"
	by (simp)
      then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb. valid_sop sop" and
	valid_sops_drop: "\<forall>sop\<in>write_sops ?drop_sb. valid_sop sop"
	apply (simp only: write_sops_append)
	apply auto
	done
	  
      from read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "distinct_read_tmps (?take_sb@?drop_sb)"
	by (simp)
      then obtain 
	read_tmps_take_drop: "read_tmps ?take_sb \<inter> read_tmps ?drop_sb = {}" and
	distinct_read_tmps_drop: "distinct_read_tmps ?drop_sb"
	by (simp only: distinct_read_tmps_append)
      
      from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop h_consis]	  
      have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b ?drop_sb) ?drop_sb"
	by (simp add: last_prog_hd_prog)

      have rel_eq: "release ?drop_sb (dom \<S>) (release  ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b) = 
                       release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b"
      proof -
        from release_append [of ?take_sb ?drop_sb]
        have "release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b =
                release ?drop_sb (dom (share ?take_sb \<S>\<^sub>s\<^sub>b)) (release  ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
          by simp
        also
        have dist: "ownership_distinct ts\<^sub>s\<^sub>b" by fact
        have consis: "sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b" by fact

        have "release ?drop_sb (dom (share ?take_sb \<S>\<^sub>s\<^sub>b)) (release  ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b) =
              release ?drop_sb (dom \<S>) (release  ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b) "
          apply (simp only: \<S>)
          apply (rule release_shared_exchange_weak [rule_format, OF _ weak_consis_drop])
          apply (rule share_all_until_volatile_write_thread_local [OF dist consis i_bound ts\<^sub>s\<^sub>b_i, symmetric])
          using acquired_all_acquired [of True ?take_sb \<O>\<^sub>s\<^sub>b] all_acquired_append [of ?take_sb ?drop_sb]
          by auto
        finally
        show ?thesis by simp
      qed
      
      from flush_store_buffer [OF i_bound' is_sim [simplified suspends]
	cph ts_i [simplified suspends] refl lp reads_consis_m hist_consis' 
	valid_sops_drop distinct_read_tmps_drop no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], of \<S>]
      show ?thesis by (simp add: acquired_take_drop [where pending_write=True, simplified] \<D>\<^sub>s\<^sub>b rel_eq)
    qed

    from safe_reach_safe_rtrancl [OF safe_reach steps_flush_sb]
    have safe_ts': "safe_delayed (?ts', flush ?drop_sb m, share ?drop_sb \<S>)".
    from safe_delayedE [OF safe_ts' i_bound_ts' ts'_i] 
    have safe_memop_flush_sb: "map owned ?ts',map released ?ts',i\<turnstile> 
      (is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b, flush ?drop_sb m, \<D>\<^sub>s\<^sub>b,acquired True sb \<O>\<^sub>s\<^sub>b,
        share ?drop_sb \<S>) \<surd>".


    
    from acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b 
    have acquired_take_sb: "acquired True ?take_sb \<O>\<^sub>s\<^sub>b \<subseteq> \<O>\<^sub>s\<^sub>b \<union> all_acquired ?take_sb ".

(* FIXME delete
    from share_takeWhile_non_volatile_Write\<^sub>s\<^sub>b
    have share_take_sb: "share ?take_sb \<S>\<^sub>s\<^sub>b = 
      \<S>\<^sub>s\<^sub>b \<ominus>\<^bsub>(all_acquired ?take_sb)\<^esub> all_unshared ?take_sb".

    from sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]
    have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb".

    with sharing_consistent_append [where xs="?take_sb" and ys="?drop_sb", of \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b]
    have sharing_consis_drop_sb: 
      "sharing_consistent (share ?take_sb \<S>\<^sub>s\<^sub>b) (acquired True ?take_sb \<O>\<^sub>s\<^sub>b) ?drop_sb"
      by (simp add: acquired_take_sb share_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)

    from read_only_takeWhile_dropWhile_share_all_until_volatile_write [OF i_bound ts\<^sub>s\<^sub>b_i]
    have read_only_drop:
      "read_only (share ?drop_sb \<S>) \<subseteq> read_only (share sb \<S>\<^sub>s\<^sub>b)"
      by (simp add: \<S>)
  *)  
    from sbh_step 
    show ?thesis
    proof (cases)
      case (SBHReadBuffered a v volatile t)
      then obtain 
	"is\<^sub>s\<^sub>b": "is\<^sub>s\<^sub>b = Read volatile a t # is\<^sub>s\<^sub>b'" and
	\<O>\<^sub>s\<^sub>b': "\<O>\<^sub>s\<^sub>b'=\<O>\<^sub>s\<^sub>b" and 
	\<D>\<^sub>s\<^sub>b': "\<D>\<^sub>s\<^sub>b'=\<D>\<^sub>s\<^sub>b" and
	\<theta>\<^sub>s\<^sub>b': "\<theta>\<^sub>s\<^sub>b' = \<theta>\<^sub>s\<^sub>b(t\<mapsto>v)" and
	sb': "sb'=sb@[Read\<^sub>s\<^sub>b volatile a t v]" and
	m\<^sub>s\<^sub>b': "m\<^sub>s\<^sub>b' = m\<^sub>s\<^sub>b" and
	\<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'=\<S>\<^sub>s\<^sub>b" and
        \<R>\<^sub>s\<^sub>b': "\<R>\<^sub>s\<^sub>b'=\<R>\<^sub>s\<^sub>b" and
	buf_v: "buffered_val sb a = Some v" 
	by auto


      from safe_memop_flush_sb [simplified is\<^sub>s\<^sub>b]  
      obtain access_cond': "a \<in> acquired True sb \<O>\<^sub>s\<^sub>b \<or> 
	a \<in> read_only (share ?drop_sb \<S>) \<or> 
	(volatile \<and> a \<in> dom (share ?drop_sb \<S>))" and
	volatile_clean: "volatile \<longrightarrow> \<not> \<D>\<^sub>s\<^sub>b" and
        rels_cond: "\<forall>j < length ts. i\<noteq>j \<longrightarrow> released (ts!j) a \<noteq> Some False" and
        rels_nv_cond: "\<not>volatile \<longrightarrow> (\<forall>j < length ts. i\<noteq>j \<longrightarrow> a \<notin> dom (released (ts!j)))"
	by cases auto

      from clean_no_outstanding_volatile_Write\<^sub>s\<^sub>b [OF i_bound ts\<^sub>s\<^sub>b_i] volatile_clean
      have volatile_cond: "volatile \<longrightarrow> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb ={}"
	by auto
      
      from buffered_val_witness [OF buf_v] obtain volatile' sop' A' L' R' W'
	where
	witness: "Write\<^sub>s\<^sub>b volatile' a sop' v A' L' R' W' \<in> set sb"
	by auto

      (* FIXME: since this is the buffered-val case, there should be a simpler proof not involving simulation to an
         unsafe state. Then we would not have to repeat the proof.*)

      {
	fix j p\<^sub>j "is\<^sub>s\<^sub>b\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>s\<^sub>b\<^sub>j \<theta>\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j
	assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	assume neq_i_j: "i \<noteq> j"
	assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j, \<theta>\<^sub>s\<^sub>b\<^sub>j, sb\<^sub>j, \<D>\<^sub>s\<^sub>b\<^sub>j, \<O>\<^sub>j,\<R>\<^sub>j)"
	assume non_vol: "\<not> volatile"
	have "a \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	proof 
	  assume a_j: "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	  let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	  let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"


          from ts_sim [rule_format, OF j_bound] jth
	  obtain suspends\<^sub>j "is\<^sub>j" \<D>\<^sub>j where
	    suspends\<^sub>j: "suspends\<^sub>j = ?drop_sb\<^sub>j" and
	    is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
	    \<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
	    ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j, 
	    \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), 
	    \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	    by (auto simp add: Let_def)
	    

	  from a_j ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
	  have a_notin_sb: "a \<notin> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
	    by auto
	  with acquired_all_acquired [of True sb \<O>\<^sub>s\<^sub>b]
	  have a_not_acq: "a \<notin> acquired True sb \<O>\<^sub>s\<^sub>b" by blast
	  with access_cond' non_vol
	  have a_ro: "a \<in> read_only (share ?drop_sb \<S>)"
	    by auto
          from read_only_share_unowned_in [OF weak_consis_drop a_ro] a_notin_sb
            acquired_all_acquired [of True ?take_sb \<O>\<^sub>s\<^sub>b]
            all_acquired_append [of ?take_sb ?drop_sb]
          have a_ro_shared: "a \<in> read_only \<S>"
            by auto

          from rels_nv_cond [rule_format, OF non_vol j_bound [simplified leq] neq_i_j] ts\<^sub>j
          have "a \<notin> dom (release ?take_sb\<^sub>j (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>j)"
            by auto
          with dom_release_takeWhile [of sb\<^sub>j "(dom (\<S>\<^sub>s\<^sub>b))" \<R>\<^sub>j]
          obtain
            a_rels\<^sub>j: "a \<notin> dom \<R>\<^sub>j" and
            a_shared\<^sub>j: "a \<notin> all_shared ?take_sb\<^sub>j"
            by auto
          
          
          have "a \<notin> \<Union>((\<lambda>(_, _, _, sb, _, _, _). all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) `
                 set ts\<^sub>s\<^sub>b)"
          proof -
            {
              fix k p\<^sub>k "is\<^sub>k" \<theta>\<^sub>k sb\<^sub>k \<D>\<^sub>k \<O>\<^sub>k \<R>\<^sub>k 
              assume k_bound: "k < length ts\<^sub>s\<^sub>b" 
              assume ts_k: "ts\<^sub>s\<^sub>b ! k = (p\<^sub>k,is\<^sub>k,\<theta>\<^sub>k,sb\<^sub>k,\<D>\<^sub>k,\<O>\<^sub>k,\<R>\<^sub>k)" 
              assume a_in: "a \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k)"
              have False
              proof (cases "k=j")
                case True with a_shared\<^sub>j jth ts_k a_in show False by auto
              next
                case False
                from ownership_distinct [OF j_bound k_bound False [symmetric] jth ts_k] a_j
                have "a \<notin> (\<O>\<^sub>k \<union> all_acquired sb\<^sub>k)" by auto
                with all_shared_acquired_or_owned [OF sharing_consis [OF k_bound ts_k]] a_in
                show False 
                using all_acquired_append [of "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k" 
                  "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k"] 
                  all_shared_append [of "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k" 
                  "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k"] by auto 
              qed
            }
            thus ?thesis by (fastforce simp add: in_set_conv_nth)
          qed
          with a_ro_shared
            read_only_shared_all_until_volatile_write_subset' [of ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b]
          have a_ro_shared\<^sub>s\<^sub>b: "a \<in> read_only \<S>\<^sub>s\<^sub>b"
            by (auto simp add: \<S>)
          
	  with read_only_unowned [OF j_bound jth]
	  have a_notin_owns_j: "a \<notin> \<O>\<^sub>j"
	    by auto


	  have own_dist: "ownership_distinct ts\<^sub>s\<^sub>b" by fact
	  have share_consis: "sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b" by fact
	  from sharing_consistent_share_all_until_volatile_write [OF own_dist share_consis i_bound ts\<^sub>s\<^sub>b_i]
	  have consis': "sharing_consistent \<S> (acquired True ?take_sb \<O>\<^sub>s\<^sub>b) ?drop_sb"
	    by (simp add: \<S>)
          from  share_all_until_volatile_write_thread_local [OF own_dist share_consis j_bound jth a_j] a_ro_shared
          have a_ro_take: "a \<in> read_only (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
            by (auto simp add: domIff \<S> read_only_def)
          from sharing_consis [OF j_bound jth]
          have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
          from sharing_consistent_weak_sharing_consistent [OF this] weak_sharing_consistent_append [of \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
          have weak_consis_drop:"weak_sharing_consistent \<O>\<^sub>j ?take_sb\<^sub>j"
            by auto
          from read_only_share_acquired_all_shared [OF this read_only_unowned [OF j_bound jth] a_ro_take ] a_notin_owns_j a_shared\<^sub>j
          have "a \<notin> all_acquired ?take_sb\<^sub>j"
            by auto
	  with a_j a_notin_owns_j
	  have a_drop: "a \<in> all_acquired ?drop_sb\<^sub>j"
	    using all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	    by simp
	  

	  from i_bound j_bound leq have j_bound_ts': "j < length ?ts'"
	    by auto

	  note conflict_drop = a_drop [simplified suspends\<^sub>j [symmetric]]
	  from split_all_acquired_in [OF conflict_drop]
	    (* FIXME: exract common parts *)
	  show False
	  proof 
	    assume "\<exists>sop a' v ys zs A L R W. 
              (suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W# zs) \<and> a \<in> A"
	    then 
	    obtain a' sop' v' ys zs A' L' R' W' where
	      split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# zs" 
	      (is "suspends\<^sub>j = ?suspends") and
		a_A': "a \<in> A'"
	      by blast

	    from sharing_consis [OF j_bound jth]
	    have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	    then have A'_R': "A' \<inter> R' = {}" 
	      by (simp add: sharing_consistent_append [of _ _ ?take_sb\<^sub>j ?drop_sb\<^sub>j, simplified] 
		suspends\<^sub>j [symmetric] split_suspends\<^sub>j sharing_consistent_append)
	    from valid_program_history [OF j_bound jth] 
	    have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	    then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
	      apply -
	      apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply (simp add: split_suspends\<^sub>j)
	      done

	    from ts\<^sub>j neq_i_j j_bound 
	    have ts'_j: "?ts'!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
	      \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), 
	      \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j, release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	      by auto
	    from valid_last_prog [OF j_bound jth] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	    then
	    have lp: "last_prog p\<^sub>j suspends\<^sub>j = p\<^sub>j"
	      apply -
	      apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done
	    from valid_reads [OF j_bound jth]
	    have reads_consis_j: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	    from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> j_bound 
	      jth reads_consis_j]
	    have reads_consis_m_j: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
	      by (simp add: m suspends\<^sub>j)


	    from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
	    have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
	      by (simp add: suspends\<^sub>j)
	    from reads_consistent_flush_independent [OF this reads_consis_m_j]
	    have reads_consis_flush_suspend: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
	      (flush ?drop_sb m) suspends\<^sub>j".
	    hence reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
	      (flush ?drop_sb m) (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'])"
	      by (simp add: split_suspends\<^sub>j reads_consistent_append)

	    from valid_write_sops [OF j_bound jth]
	    have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
	      valid_sops_drop: "\<forall>sop\<in>write_sops (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']). valid_sop sop"
	      apply (simp only: write_sops_append)
	      apply auto
	      done

	    from read_tmps_distinct [OF j_bound jth]
	    have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    then obtain 
	      read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
	      distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      apply (simp only: distinct_read_tmps_append)
	      done

	    from valid_history [OF j_bound jth]
	    have h_consis: 
	      "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done
	    
	    have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	    proof -
	      from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		by simp
	      from last_prog_hd_prog_append' [OF h_consis] this
	      have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      moreover 
	      have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		by (rule last_prog_hd_prog_append)
	      ultimately show ?thesis
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	    qed

	    from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
	      h_consis] last_prog_hd_prog
	    have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    from reads_consistent_drop_volatile_writes_no_volatile_reads  
	    [OF reads_consis_j] 
	    have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b 
	      (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) = {}"
	      by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		split_suspends\<^sub>j )

	    have acq_simp:
	      "acquired True (ys @ [Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) 
              (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) = 
              acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R'"
	      by (simp add: acquired_append)

	    from flush_store_buffer_append [where sb="ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']" and sb'="zs", simplified,
	      OF j_bound_ts' is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
	      ts'_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_ys 
	      hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
	      distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
	      no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
	      \<S>="share ?drop_sb \<S>"]

	    obtain is\<^sub>j' \<R>\<^sub>j' where
	      is\<^sub>j': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs" and
	      steps_ys: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>)  \<Rightarrow>\<^sub>d\<^sup>* 
	      (?ts'[j:=(last_prog
              (hd_prog p\<^sub>j (Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# zs)) (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']),
              is\<^sub>j',
              \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps zs),
              (), True, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R',\<R>\<^sub>j')],
              flush (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) (flush ?drop_sb m),
              share (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) (share ?drop_sb \<S>))"
	      (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")

              by (auto simp add: acquired_append outstanding_refs_append)

	    from i_bound' have i_bound_ys: "i < length ?ts_ys"
	      by auto

	    from i_bound' neq_i_j 
	    have ts_ys_i: "?ts_ys!i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b,(), 
	      \<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b, release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
	      by simp
	    note conflict_computation = rtranclp_trans [OF steps_flush_sb steps_ys]
	    
	    from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	    have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	    
	    from safe_delayedE [OF this i_bound_ys ts_ys_i, simplified is\<^sub>s\<^sub>b] non_vol a_not_acq
	    have "a \<in> read_only (share (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) (share ?drop_sb \<S>))"
	      apply cases
	      apply (auto simp add: Let_def is\<^sub>s\<^sub>b)
	      done

	    with a_A'
	    show False
	      by (simp add: share_append in_read_only_convs)
	  next
	    assume "\<exists>A L R W ys zs. suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A L R W # zs \<and> a \<in> A"
	    then 
	    obtain A' L' R' W' ys zs where
	      split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs" 
	      (is "suspends\<^sub>j = ?suspends") and
		a_A': "a \<in> A'"
	      by blast

	    from valid_program_history [OF j_bound jth] 
	    have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	    then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
	      apply -
	      apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply (simp add: split_suspends\<^sub>j)
	      done

	    from ts\<^sub>j neq_i_j j_bound 
	    have ts'_j: "?ts'!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
	      \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), 
	      \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j, release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	      by auto
	    from valid_last_prog [OF j_bound jth] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	    then
	    have lp: "last_prog p\<^sub>j suspends\<^sub>j = p\<^sub>j"
	      apply -
	      apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done


	    from valid_reads [OF j_bound jth]
	    have reads_consis_j: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	    from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> j_bound 
	      jth reads_consis_j]
	    have reads_consis_m_j: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
	      by (simp add: m suspends\<^sub>j)

	    from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
	    have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
	      by (simp add: suspends\<^sub>j)
	    from reads_consistent_flush_independent [OF this reads_consis_m_j]
	    have reads_consis_flush_suspend: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
	      (flush ?drop_sb m) suspends\<^sub>j".

	    hence reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)  
	      (flush ?drop_sb m) (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W'])"
	      by (simp add: split_suspends\<^sub>j reads_consistent_append)
	    from valid_write_sops [OF j_bound jth]
	    have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
	      valid_sops_drop: "\<forall>sop\<in>write_sops (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']). valid_sop sop"
	      apply (simp only: write_sops_append)
	      apply auto
	      done

	    from read_tmps_distinct [OF j_bound jth]
	    have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    then obtain 
	      read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
	      distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      apply (simp only: distinct_read_tmps_append)
	      done

	    from valid_history [OF j_bound jth]
	    have h_consis: 
	      "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done
	    
	    have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	    proof -
	      from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		by simp
	      from last_prog_hd_prog_append' [OF h_consis] this
	      have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      moreover 
	      have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		by (rule last_prog_hd_prog_append)
	      ultimately show ?thesis
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	    qed

	    from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
	      h_consis] last_prog_hd_prog
	    have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    from reads_consistent_drop_volatile_writes_no_volatile_reads  
	    [OF reads_consis_j] 
	    have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b 
	      (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) = {}"
	      by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		split_suspends\<^sub>j )

	    have acq_simp:
	      "acquired True (ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W']) 
              (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) = 
              acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R'"
	      by (simp add: acquired_append)

	    from flush_store_buffer_append [where sb="ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']" and sb'="zs", simplified,
	      OF j_bound_ts' is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
	      ts'_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_ys 
	      hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
	      distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
	      no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
	      \<S>="share ?drop_sb \<S>"]
	    obtain is\<^sub>j' \<R>\<^sub>j' where
	      is\<^sub>j': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs" and
	      steps_ys: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>)  \<Rightarrow>\<^sub>d\<^sup>* 
	      (?ts'[j:=(last_prog
              (hd_prog p\<^sub>j (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)) (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']),
              is\<^sub>j',
              \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps zs),
              (),
              \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W']) \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R',\<R>\<^sub>j')],
              flush (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) (flush ?drop_sb m),
              share (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) (share ?drop_sb \<S>))"
	      (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
              by (auto simp add: acquired_append)

	    from i_bound' have i_bound_ys: "i < length ?ts_ys"
	      by auto

	    from i_bound' neq_i_j 
	    have ts_ys_i: "?ts_ys!i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b,\<theta>\<^sub>s\<^sub>b,(), 
	      \<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b, release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
	      by simp
	    note conflict_computation = rtranclp_trans [OF steps_flush_sb steps_ys]
	    
	    from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	    have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	    
	    from safe_delayedE [OF this i_bound_ys ts_ys_i, simplified is\<^sub>s\<^sub>b] non_vol a_not_acq
	    have "a \<in> read_only (share (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) (share ?drop_sb \<S>))"
	      apply cases
	      apply (auto simp add: Let_def is\<^sub>s\<^sub>b)
	      done

	    with a_A'
	    show False
	      by (simp add: share_append in_read_only_convs)
	  qed
	qed
      }
      note non_volatile_unowned_others = this

      {
        assume a_in: "a \<in> read_only (share (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>)"
        assume nv: "\<not> volatile"
        have "a \<in> read_only (share sb \<S>\<^sub>s\<^sub>b)"
        proof (cases "a \<in> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb")
          case True
          from share_all_until_volatile_write_thread_local' [OF ownership_distinct_ts\<^sub>s\<^sub>b 
            sharing_consis_ts\<^sub>s\<^sub>b i_bound ts\<^sub>s\<^sub>b_i True] True a_in
          show ?thesis
            by (simp add: \<S> read_only_def)
        next
          case False
          from read_only_share_unowned [OF weak_consis_drop _ a_in] False 
            acquired_all_acquired [of True ?take_sb \<O>\<^sub>s\<^sub>b] all_acquired_append [of ?take_sb ?drop_sb]
          have a_ro_shared: "a \<in> read_only \<S>"
            by auto
          
          have "a \<notin> \<Union>((\<lambda>(_, _, _, sb, _, _, _).
               all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts\<^sub>s\<^sub>b)"
          proof -
            {
              fix k p\<^sub>k "is\<^sub>k" \<theta>\<^sub>k sb\<^sub>k \<D>\<^sub>k \<O>\<^sub>k \<R>\<^sub>k 
              assume k_bound: "k < length ts\<^sub>s\<^sub>b" 
              assume ts_k: "ts\<^sub>s\<^sub>b ! k = (p\<^sub>k,is\<^sub>k,\<theta>\<^sub>k,sb\<^sub>k,\<D>\<^sub>k,\<O>\<^sub>k,\<R>\<^sub>k)" 
              assume a_in: "a \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k)"
              have False
              proof (cases "k=i")
                case True with False ts\<^sub>s\<^sub>b_i ts_k a_in 
                  all_shared_acquired_or_owned [OF sharing_consis [OF k_bound ts_k]]     
                  all_shared_append [of "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k" 
                  "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k"] show False by auto
              next
                case False
                from rels_nv_cond [rule_format, OF nv k_bound [simplified leq] False [symmetric] ] 
                ts_sim [rule_format, OF k_bound] ts_k
                have "a \<notin> dom (release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k) (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>k)"
                  by (auto simp add: Let_def)
                with dom_release_takeWhile [of sb\<^sub>k "(dom (\<S>\<^sub>s\<^sub>b))" \<R>\<^sub>k]
                obtain
                  a_rels\<^sub>j: "a \<notin> dom \<R>\<^sub>k" and
                  a_shared\<^sub>j: "a \<notin> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k)"
                  by auto
                with False a_in show ?thesis 
                  by auto
             qed
           }      
           thus ?thesis by (fastforce simp add: in_set_conv_nth)
          qed
          with read_only_shared_all_until_volatile_write_subset' [of ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b] a_ro_shared
          have "a \<in> read_only \<S>\<^sub>s\<^sub>b"
            by (auto simp add: \<S>)
          from read_only_share_unowned' [OF weak_consis_sb read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] False  this]
          show ?thesis .
        qed
      } note non_vol_ro_reduction = this

      have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof (cases volatile)
	  case False
	  from outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i]
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb".
	  then

	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb@[Read\<^sub>s\<^sub>b False a t v])"
	    using  access_cond' False non_vol_ro_reduction
	    by (auto simp add: non_volatile_owned_or_read_only_append)
            
	  from outstanding_non_volatile_refs_owned_or_read_only_nth_update [OF i_bound this]
	  show ?thesis by (auto simp add: False ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	next
	  case True
	  from outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i]  
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb".
	  then
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb@[Read\<^sub>s\<^sub>b True a t v])"
	    using True
	    by (simp add: non_volatile_owned_or_read_only_append)
	  from outstanding_non_volatile_refs_owned_or_read_only_nth_update [OF i_bound this]
	  show ?thesis by (auto simp add: True ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	qed
      next
	show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'"
	proof -
	  have out: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb @ [Read\<^sub>s\<^sub>b volatile a t v]) \<subseteq> 
            outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb"
	    by (auto simp add: outstanding_refs_append)
	  have "all_acquired (sb @ [Read\<^sub>s\<^sub>b volatile a t v]) \<subseteq> all_acquired sb"
	    by (auto simp add: all_acquired_append)
	  from outstanding_volatile_writes_unowned_by_others_store_buffer 
	  [OF i_bound ts\<^sub>s\<^sub>b_i out this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b')
	qed
      next
	show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
	proof (cases volatile)
	  case True
	  have r: "read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Read\<^sub>s\<^sub>b volatile a t v])) \<O>\<^sub>s\<^sub>b)
                    (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Read\<^sub>s\<^sub>b volatile a t v]))
                \<subseteq> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>\<^sub>s\<^sub>b)
                    (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
	    apply (case_tac "outstanding_refs (is_volatile_Write\<^sub>s\<^sub>b) sb = {}")
	    apply (simp_all add: outstanding_vol_write_take_drop_appends
	    acquired_append read_only_reads_append True)
	    done

	  have "\<O>\<^sub>s\<^sub>b \<union> all_acquired (sb @ [Read\<^sub>s\<^sub>b volatile a t v]) \<subseteq> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
	    by (simp add: all_acquired_append)

	 
	  from  read_only_reads_unowned_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i r this]
	  show ?thesis
	    by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb')
	next
	  case False
	  show ?thesis
	  proof (unfold_locales)
	    fix n m
	    fix p\<^sub>n "is\<^sub>n" \<O>\<^sub>n \<R>\<^sub>n \<D>\<^sub>n \<theta>\<^sub>n sb\<^sub>n p\<^sub>m "is\<^sub>m" \<O>\<^sub>m \<R>\<^sub>m \<D>\<^sub>m \<theta>\<^sub>m sb\<^sub>m
	    assume n_bound: "n < length ts\<^sub>s\<^sub>b'"
	    and m_bound: "m < length ts\<^sub>s\<^sub>b'"
	    and neq_n_m: "n\<noteq>m"
	    and nth: "ts\<^sub>s\<^sub>b'!n = (p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n, \<R>\<^sub>n)"
	    and mth: "ts\<^sub>s\<^sub>b'!m =(p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m, \<R>\<^sub>m)"
	    from n_bound have n_bound': "n < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')
	    from m_bound have m_bound': "m < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')

	    have acq_eq: "(\<O>\<^sub>s\<^sub>b' \<union> all_acquired sb') = (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb)"
	      by (simp add: all_acquired_append sb' \<O>\<^sub>s\<^sub>b')	      

	    show "(\<O>\<^sub>m \<union> all_acquired sb\<^sub>m) \<inter>
              read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) \<O>\<^sub>n)
              (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) =
              {}"
	    proof (cases "m=i")
	      case True
	      with neq_n_m have neq_n_i: "n\<noteq>i"
		by auto
		
	      with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n, \<R>\<^sub>n)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      note read_only_reads_unowned [OF n_bound' i_bound  neq_n_i nth' ts\<^sub>s\<^sub>b_i]
	      moreover
	      note acq_eq
	      ultimately show ?thesis
		using True ts\<^sub>s\<^sub>b_i nth mth n_bound' m_bound'
		by (simp add: ts\<^sub>s\<^sub>b')
	    next
	      case False
	      note neq_m_i = this
	      with m_bound mth i_bound have mth': "ts\<^sub>s\<^sub>b!m = (p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m,\<R>\<^sub>m)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      show ?thesis
	      proof (cases "n=i")
		case True
		note read_only_reads_unowned [OF i_bound m_bound' neq_m_i [symmetric] ts\<^sub>s\<^sub>b_i mth']
		moreover 
		note acq_eq
		moreover
		note non_volatile_unowned_others [OF m_bound' neq_m_i [symmetric] mth']
		ultimately show ?thesis
		  using True ts\<^sub>s\<^sub>b_i nth mth n_bound' m_bound' neq_m_i
		  apply (case_tac "outstanding_refs (is_volatile_Write\<^sub>s\<^sub>b) sb = {}")
		  apply (clarsimp simp add: outstanding_vol_write_take_drop_appends
		    acquired_append read_only_reads_append ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b')+
		  done
	      next
		case False
		with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n, \<R>\<^sub>n)"
		  by (auto simp add: ts\<^sub>s\<^sub>b')
		from read_only_reads_unowned [OF n_bound' m_bound' neq_n_m  nth' mth'] False neq_m_i
		show ?thesis 
		  by (clarsimp)
	      qed
	    qed
	  qed
	qed
      next
	show "ownership_distinct ts\<^sub>s\<^sub>b'"
	proof -
	  have "all_acquired (sb @ [Read\<^sub>s\<^sub>b volatile a t v]) \<subseteq> all_acquired sb"
	    by (auto simp add: all_acquired_append)
	  from ownership_distinct_instructions_read_value_store_buffer_independent 
	  [OF i_bound ts\<^sub>s\<^sub>b_i this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b')
	qed
      qed


      have valid_hist': "valid_history program_step ts\<^sub>s\<^sub>b'"
      proof -
	from valid_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have hcons: "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b sb) sb".
	from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have t_notin_reads: "t \<notin> read_tmps sb"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	from load_tmps_write_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have t_notin_writes: "t \<notin> \<Union>(fst ` write_sops sb)"
	  by (auto simp add: "is\<^sub>s\<^sub>b")

	from valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	have valid_sops: "\<forall>sop \<in> write_sops sb. valid_sop sop"
	  by auto
	from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i]
	have t_fresh: "t \<notin> dom \<theta>\<^sub>s\<^sub>b"
	  using "is\<^sub>s\<^sub>b"
	  by simp
	have "history_consistent (\<theta>\<^sub>s\<^sub>b(t\<mapsto>v)) 
	       (hd_prog p\<^sub>s\<^sub>b (sb@ [Read\<^sub>s\<^sub>b volatile a t v])) (sb@ [Read\<^sub>s\<^sub>b volatile a t v])"
	  using t_notin_writes valid_sops t_fresh hcons
	  valid_implies_valid_prog_hd [OF i_bound ts\<^sub>s\<^sub>b_i valid]
	  apply -
	  apply (rule history_consistent_appendI)
	  apply (auto simp add: hd_prog_append_Read\<^sub>s\<^sub>b)
	  done
	from valid_history_nth_update [OF i_bound this]
	show ?thesis
	  by (auto simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
      qed

      from reads_consistent_buffered_snoc [OF buf_v valid_reads [OF i_bound ts\<^sub>s\<^sub>b_i] 
	volatile_cond] 
      have reads_consis': "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b (sb @ [Read\<^sub>s\<^sub>b volatile a t v])"
	by (simp split: if_split_asm)

      from valid_reads_nth_update [OF i_bound this]
      have valid_reads': "valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b')

      have valid_sharing': "valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)	
	from outstanding_non_volatile_writes_unshared [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b (sb @ [Read\<^sub>s\<^sub>b volatile a t v])"
	  by (auto simp add: non_volatile_writes_unshared_append)
	from outstanding_non_volatile_writes_unshared_nth_update [OF i_bound this]
	show "outstanding_non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' sb' \<S>\<^sub>s\<^sub>b')
      next
	from sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb".
	then
	have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb @ [Read\<^sub>s\<^sub>b volatile a t v])"
	  by (simp add:  sharing_consistent_append)
	from sharing_consis_nth_update [OF i_bound this]
	show "sharing_consis \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' \<S>\<^sub>s\<^sub>b')
      next
	note read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i]
	from read_only_unowned_nth_update [OF i_bound this]
	show "read_only_unowned \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b')
      next
	from unowned_shared_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i subset_refl]
	show "unowned_shared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next
	from no_outstanding_write_to_read_only_memory [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b sb".
	hence "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b (sb@[Read\<^sub>s\<^sub>b volatile a t v])"
	  by (simp add: no_write_to_read_only_memory_append)
	from no_outstanding_write_to_read_only_memory_nth_update [OF i_bound this]
	show "no_outstanding_write_to_read_only_memory \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' sb')
      qed

      have tmps_distinct': "tmps_distinct ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_load_tmps is\<^sub>s\<^sub>b'"
	  by (auto split: instr.splits simp add: is\<^sub>s\<^sub>b)
	from load_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b')
      next
	from read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_read_tmps sb".
	moreover
	from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "t \<notin> read_tmps sb"
	  by (auto simp add: is\<^sub>s\<^sub>b)
	ultimately have "distinct_read_tmps (sb @ [Read\<^sub>s\<^sub>b volatile a t v])"
	  by (auto simp add: distinct_read_tmps_append)
	from read_tmps_distinct_nth_update [OF i_bound this]
	show "read_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb')
      next
	from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] 
          load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> read_tmps (sb @ [Read\<^sub>s\<^sub>b volatile a t v]) = {}"
	  by (clarsimp simp add: read_tmps_append "is\<^sub>s\<^sub>b")
	from load_tmps_read_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_read_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      have valid_sops': "valid_sops ts\<^sub>s\<^sub>b'"
      proof -
	from valid_store_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	have valid_store_sops': "\<forall>sop\<in>store_sops is\<^sub>s\<^sub>b'. valid_sop sop"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	from valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	have valid_write_sops': "\<forall>sop\<in>write_sops (sb@ [Read\<^sub>s\<^sub>b volatile a t v]). valid_sop sop"
	  by (auto simp add: write_sops_append)
	from valid_sops_nth_update [OF i_bound  valid_write_sops' valid_store_sops']
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      have valid_dd': "valid_data_dependency ts\<^sub>s\<^sub>b'"
      proof -
	from data_dependency_consistent_instrs [OF i_bound ts\<^sub>s\<^sub>b_i]
	have dd_is: "data_dependency_consistent_instrs (dom \<theta>\<^sub>s\<^sub>b') is\<^sub>s\<^sub>b'"
	  by (auto simp add: "is\<^sub>s\<^sub>b" \<theta>\<^sub>s\<^sub>b')
	from load_tmps_write_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> \<Union>(fst ` write_sops (sb@ [Read\<^sub>s\<^sub>b volatile a t v])) = {}"
	  by (auto simp add: write_sops_append "is\<^sub>s\<^sub>b")
	from valid_data_dependency_nth_update [OF i_bound dd_is this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      have load_tmps_fresh': "load_tmps_fresh ts\<^sub>s\<^sub>b'"
      proof -
	from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "load_tmps (Read volatile a t # is\<^sub>s\<^sub>b') \<inter> dom \<theta>\<^sub>s\<^sub>b = {}"
	  by (simp add: "is\<^sub>s\<^sub>b")
	moreover
	from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] have "t \<notin> load_tmps is\<^sub>s\<^sub>b'"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	ultimately have "load_tmps is\<^sub>s\<^sub>b' \<inter> dom (\<theta>\<^sub>s\<^sub>b(t \<mapsto> v)) = {}"
	  by auto
	from load_tmps_fresh_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<theta>\<^sub>s\<^sub>b')
      qed

      have enough_flushs': "enough_flushs ts\<^sub>s\<^sub>b'"
      proof -
	from clean_no_outstanding_volatile_Write\<^sub>s\<^sub>b [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "\<not> \<D>\<^sub>s\<^sub>b \<longrightarrow> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Read\<^sub>s\<^sub>b volatile a t v]) = {}"
	  by (auto simp add: outstanding_refs_append )
	from enough_flushs_nth_update [OF i_bound this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' sb' \<D>\<^sub>s\<^sub>b')
      qed
	
      have valid_program_history': "valid_program_history ts\<^sub>s\<^sub>b'"
      proof -	
	from valid_program_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "causal_program_history is\<^sub>s\<^sub>b sb" .
	then have causal': "causal_program_history is\<^sub>s\<^sub>b' (sb@[Read\<^sub>s\<^sub>b volatile a t v])"
	  by (auto simp: causal_program_history_Read  "is\<^sub>s\<^sub>b")
	from valid_last_prog [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "last_prog p\<^sub>s\<^sub>b sb = p\<^sub>s\<^sub>b".
	hence "last_prog p\<^sub>s\<^sub>b (sb @ [Read\<^sub>s\<^sub>b volatile a t v]) = p\<^sub>s\<^sub>b"
	  by (simp add: last_prog_append_Read\<^sub>s\<^sub>b)

	from valid_program_history_nth_update [OF i_bound causal' this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed
      show ?thesis
      proof (cases "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}")
	case True 

	from True have flush_all: "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = sb"
	  by (auto simp add: outstanding_refs_conv )

	from True have suspend_nothing: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = []"
	  by (auto simp add: outstanding_refs_conv)

	hence suspends_empty: "suspends = []"
	  by (simp add: suspends)
	from suspends_empty is_sim have "is": "is = Read volatile a t # is\<^sub>s\<^sub>b'"
	  by (simp add: "is\<^sub>s\<^sub>b")
	with suspends_empty ts_i 
	have ts_i: "ts!i = (p\<^sub>s\<^sub>b, Read volatile a t # is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b,(), \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b, release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
	  by simp

	from direct_memop_step.Read 
	have "(Read volatile a t # is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), m, \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,
                release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b, \<S>) \<rightarrow> 
          (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t \<mapsto> m a), (), m, \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b, \<S>)".
	from direct_computation.concurrent_step.Memop [OF i_bound' ts_i this]
	have "(ts, m, \<S>) \<Rightarrow>\<^sub>d (ts[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b',  \<theta>\<^sub>s\<^sub>b(t \<mapsto> m a), (),
               \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b, release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)], m, \<S>)" . 

	moreover
	
	from flush_all_until_volatile_write_Read_commute [OF i_bound ts\<^sub>s\<^sub>b_i [simplified "is\<^sub>s\<^sub>b"] ]
	have flush_commute: "flush_all_until_volatile_write
          (ts\<^sub>s\<^sub>b[i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b', 
               \<theta>\<^sub>s\<^sub>b(t\<mapsto>v), sb @ [Read\<^sub>s\<^sub>b volatile a t v], \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b, \<R>\<^sub>s\<^sub>b)]) m\<^sub>s\<^sub>b =
          flush_all_until_volatile_write ts\<^sub>s\<^sub>b m\<^sub>s\<^sub>b".

	from True witness have not_volatile': "volatile' = False"
	  by (auto simp add: outstanding_refs_conv)

	from witness not_volatile' have a_out_sb: "a \<in> outstanding_refs (Not \<circ> is_volatile) sb"
	  apply (cases sop')
	  apply (fastforce simp add: outstanding_refs_conv is_volatile_def split: memref.splits)
	  done

	
	with  non_volatile_owned_or_read_only_outstanding_refs 
	[OF outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i]]
	have a_owned: "a \<in> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb \<union> read_only_reads \<O>\<^sub>s\<^sub>b sb"
	  by auto

	have "flush_all_until_volatile_write ts\<^sub>s\<^sub>b m\<^sub>s\<^sub>b a = v"
	proof - (* FIXME: Same proof as in Unbuffered case *)
          have "\<forall>j < length ts\<^sub>s\<^sub>b. i \<noteq> j \<longrightarrow>
                  (let (_,_,_,sb\<^sub>j,_,_,_) = ts\<^sub>s\<^sub>b!j 
                  in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))"
	  proof -
	    {
	      fix j p\<^sub>j "is\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	      assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	      assume neq_i_j: "i \<noteq> j"
	      assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j, xs\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j, \<R>\<^sub>j)"
	      have "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	      proof 
		let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
		let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
		assume a_in: "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b ?take_sb\<^sub>j"
		with outstanding_refs_takeWhile [where P'= "Not \<circ> is_volatile_Write\<^sub>s\<^sub>b"]
		have a_in': "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
		  by auto
		with non_volatile_owned_or_read_only_outstanding_non_volatile_writes 
		[OF outstanding_non_volatile_refs_owned_or_read_only [OF j_bound jth]]
		have j_owns: "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
		  by auto
		with ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
		have a_not_owns: "a \<notin> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
		  by blast
		

		from non_volatile_owned_or_read_only_append [of False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		  outstanding_non_volatile_refs_owned_or_read_only [OF j_bound jth]
		have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j"
		  by simp
		from non_volatile_owned_or_read_only_outstanding_non_volatile_writes [OF this] a_in
		have j_owns_drop: "a \<in> \<O>\<^sub>j \<union> all_acquired ?take_sb\<^sub>j"
		  by auto
                from rels_cond [rule_format, OF j_bound [simplified leq] neq_i_j] ts_sim [rule_format, OF j_bound] jth
                have no_unsharing:"release ?take_sb\<^sub>j (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>j  a \<noteq> Some False"
                  by (auto simp add: Let_def)

	
		{
		  assume "a \<in> acquired True sb \<O>\<^sub>s\<^sub>b"
		  with acquired_all_acquired_in [OF this] ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth] 
		    j_owns 
		  have False
		    by auto
		}
		moreover
		{
		  assume a_ro: "a \<in> read_only (share ?drop_sb \<S>)"
                  
                  from read_only_share_unowned_in [OF weak_consis_drop a_ro] a_not_owns
                  acquired_all_acquired [of True ?take_sb \<O>\<^sub>s\<^sub>b]
                  all_acquired_append [of ?take_sb ?drop_sb]
                  have "a \<in> read_only \<S>"
                    by auto
                  with share_all_until_volatile_write_thread_local [OF ownership_distinct_ts\<^sub>s\<^sub>b sharing_consis_ts\<^sub>s\<^sub>b j_bound jth j_owns]
                  have "a \<in> read_only (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
                    by (auto simp add: read_only_def \<S>)
                  hence a_dom: "a \<in> dom  (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
                    by (auto simp add: read_only_def domIff)
                  from outstanding_non_volatile_writes_unshared [OF j_bound jth]
                  non_volatile_writes_unshared_append [of \<S>\<^sub>s\<^sub>b ?take_sb\<^sub>j ?drop_sb\<^sub>j]
                  have nvw: "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b ?take_sb\<^sub>j" by auto
                  from release_not_unshared_no_write_take [OF this no_unsharing a_dom] a_in
                  have False by auto
		}
		moreover
		{
		  assume a_share: "volatile \<and> a \<in> dom (share ?drop_sb \<S>)"
		  from outstanding_non_volatile_writes_unshared [OF j_bound jth]
		  have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b sb\<^sub>j".
		  with non_volatile_writes_unshared_append [of \<S>\<^sub>s\<^sub>b "?take_sb\<^sub>j"
		  "?drop_sb\<^sub>j"]
		  have unshared_take: "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		    by clarsimp
		   
		  from valid_own have own_dist: "ownership_distinct ts\<^sub>s\<^sub>b"
		    by (simp add: valid_ownership_def)
		  from valid_sharing have "sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b"
		    by (simp add: valid_sharing_def)
		  from sharing_consistent_share_all_until_volatile_write [OF own_dist this i_bound ts\<^sub>s\<^sub>b_i]
		  have sc: "sharing_consistent \<S> (acquired True ?take_sb \<O>\<^sub>s\<^sub>b) ?drop_sb"
		    by (simp add: \<S>)
		  from sharing_consistent_share_all_shared 
		  have "dom (share ?drop_sb \<S>) \<subseteq> dom \<S> \<union> all_shared ?drop_sb"
		    by auto
		  also from sharing_consistent_all_shared [OF sc]
		  have "\<dots> \<subseteq> dom \<S> \<union> acquired True ?take_sb \<O>\<^sub>s\<^sub>b" by auto
		  also from acquired_all_acquired all_acquired_takeWhile 
		  have "\<dots> \<subseteq> dom \<S> \<union> (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb)" by force
		  finally
		  have a_shared: "a \<in> dom \<S>"
		    using a_share a_not_owns
		    by auto

                  with share_all_until_volatile_write_thread_local [OF ownership_distinct_ts\<^sub>s\<^sub>b sharing_consis_ts\<^sub>s\<^sub>b j_bound jth j_owns]
                  have a_dom: "a \<in> dom  (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
                    by (auto simp add: \<S> domIff)
                  from release_not_unshared_no_write_take [OF  unshared_take no_unsharing a_dom] a_in
                  have False by auto

		}
		ultimately show False
		  using access_cond'
		  by auto
	      qed
	    }
	    thus ?thesis
	      by (fastforce simp add: Let_def)
	  qed
	  
	  from flush_all_until_volatile_write_buffered_val_conv 
	  [OF True i_bound ts\<^sub>s\<^sub>b_i this]
	  show ?thesis
	    by (simp add: buf_v)
	qed


	hence m_a_v: "m a = v"
	  by (simp add: m)
	
	have tmps_commute: "\<theta>\<^sub>s\<^sub>b(t \<mapsto> v) = (\<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b - {t}))(t \<mapsto> v)"
	  apply (rule ext)
	  apply (auto simp add: restrict_map_def domIff)
	  done

	from suspend_nothing
	have suspend_nothing': "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') = []"
	  by (simp add: sb')

	from \<D>
	have \<D>': "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Read\<^sub>s\<^sub>b volatile a t v]) \<noteq>  {})"
	  by (auto simp: outstanding_refs_append)

	have "(ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> (ts[i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b',
                \<theta>\<^sub>s\<^sub>b(t\<mapsto>m a),(),\<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,
                release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)],m,\<S>)"
	  apply (rule sim_config.intros) 
	  apply    (simp add: m flush_commute ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb' \<D>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b')
	  using   share_all_until_volatile_write_Read_commute [OF i_bound ts\<^sub>s\<^sub>b_i [simplified is\<^sub>s\<^sub>b]]
	  apply   (simp add: \<S> \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b')
	  using  leq
	  apply  (simp add: ts\<^sub>s\<^sub>b')
	  using i_bound i_bound' ts_sim ts_i True \<D>' 
	  apply (clarsimp simp add: Let_def nth_list_update 
	    outstanding_refs_conv m_a_v  ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb' \<R>\<^sub>s\<^sub>b' suspend_nothing' 
	    \<D>\<^sub>s\<^sub>b' flush_all acquired_append release_append
	    split: if_split_asm )
	  apply (rule tmps_commute)
	  done	

	ultimately show ?thesis
	  using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct'
	    valid_sops' valid_dd' load_tmps_fresh' enough_flushs' 
            valid_program_history' valid'
	    m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b'
	  by (auto simp del: fun_upd_apply )
      next
	case False

	then obtain r where r_in: "r \<in> set sb" and volatile_r: "is_volatile_Write\<^sub>s\<^sub>b r"
	  by (auto simp add: outstanding_refs_conv)
	from takeWhile_dropWhile_real_prefix 
	[OF r_in, of  "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)", simplified, OF volatile_r] 
	obtain a' v' sb'' sop' A' L' R' W' where
	  sb_split: "sb = takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb @ Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# sb''" 
	  and
	  drop: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# sb''"
	  apply (auto)
    subgoal for y ys
	  apply (case_tac y)
	  apply auto
	  done
	  done
	from drop suspends have suspends: "suspends = Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# sb''"
	  by simp


	have "(ts, m, \<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts, m, \<S>)" by auto

	moreover

	from flush_all_until_volatile_write_Read_commute [OF i_bound ts\<^sub>s\<^sub>b_i 
	  [simplified "is\<^sub>s\<^sub>b"] ]

	have flush_commute: "flush_all_until_volatile_write
             (ts\<^sub>s\<^sub>b[i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t \<mapsto> v), sb @ [Read\<^sub>s\<^sub>b volatile a t v], \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b, \<R>\<^sub>s\<^sub>b)]) m\<^sub>s\<^sub>b =
             flush_all_until_volatile_write ts\<^sub>s\<^sub>b m\<^sub>s\<^sub>b".

	have "Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'\<in> set sb"
	  by (subst sb_split) auto
	
	from dropWhile_append1 [OF this, of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)"]
	have drop_app_comm:
	  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Read\<^sub>s\<^sub>b volatile a t v])) =
                dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb @ [Read\<^sub>s\<^sub>b volatile a t v]"
	  by simp

	from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "t \<notin> dom \<theta>\<^sub>s\<^sub>b"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	then have tmps_commute: 
	  "\<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b - read_tmps sb'') =
          \<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b - insert t (read_tmps sb''))"
	  apply -
	  apply (rule ext)
	  apply auto
	  done

	from \<D>
	have \<D>': "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Read\<^sub>s\<^sub>b volatile a t v]) \<noteq>  {})"
	  by (auto simp: outstanding_refs_append)

	have "(ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<sim> (ts,m,\<S>)"
	  apply (rule sim_config.intros) 
	  apply    (simp add: m flush_commute ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb' \<D>\<^sub>s\<^sub>b' )
	  using   share_all_until_volatile_write_Read_commute [OF i_bound ts\<^sub>s\<^sub>b_i [simplified is\<^sub>s\<^sub>b]]
	  apply   (simp add: \<S> \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
	  using  leq
	  apply  (simp add: ts\<^sub>s\<^sub>b')
	  using i_bound i_bound' ts_sim ts_i is_sim \<D>' 
	  apply (clarsimp simp add: Let_def nth_list_update is_sim drop_app_comm 
	    read_tmps_append suspends prog_instrs_append_Read\<^sub>s\<^sub>b instrs_append_Read\<^sub>s\<^sub>b 
	    hd_prog_append_Read\<^sub>s\<^sub>b
	    drop "is\<^sub>s\<^sub>b" ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' \<D>\<^sub>s\<^sub>b' acquired_append takeWhile_append1 [OF r_in] volatile_r 
	    split: if_split_asm)
	  apply (simp add: drop tmps_commute)+
	  done

	ultimately show ?thesis
	  using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' valid_dd'
	    valid_sops' load_tmps_fresh' enough_flushs' 
	    valid_program_history' valid' m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' 
	  by (auto simp del: fun_upd_apply )
      qed
    next
      case (SBHReadUnbuffered a volatile t)
      then obtain 
	"is\<^sub>s\<^sub>b": "is\<^sub>s\<^sub>b = Read volatile a t # is\<^sub>s\<^sub>b'" and
	\<O>\<^sub>s\<^sub>b': "\<O>\<^sub>s\<^sub>b'=\<O>\<^sub>s\<^sub>b" and
        \<R>\<^sub>s\<^sub>b': "\<R>\<^sub>s\<^sub>b'=\<R>\<^sub>s\<^sub>b" and
	\<theta>\<^sub>s\<^sub>b': "\<theta>\<^sub>s\<^sub>b' = \<theta>\<^sub>s\<^sub>b(t\<mapsto>(m\<^sub>s\<^sub>b a))" and
	sb': "sb'=sb@[Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)]" and
	m\<^sub>s\<^sub>b': "m\<^sub>s\<^sub>b' = m\<^sub>s\<^sub>b" and
	\<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'=\<S>\<^sub>s\<^sub>b" and 
	\<D>\<^sub>s\<^sub>b': "\<D>\<^sub>s\<^sub>b'=\<D>\<^sub>s\<^sub>b" and
	buf_None: "buffered_val sb a = None" 

	by auto


      from safe_memop_flush_sb [simplified is\<^sub>s\<^sub>b]
      obtain access_cond': "a \<in> acquired True sb \<O>\<^sub>s\<^sub>b \<or> 
	a \<in> read_only (share ?drop_sb \<S>) \<or> (volatile \<and> a \<in> dom (share ?drop_sb \<S>))" and
	volatile_clean: "volatile \<longrightarrow> \<not> \<D>\<^sub>s\<^sub>b" and
        rels_cond: "\<forall>j < length ts. i\<noteq>j \<longrightarrow> released (ts!j) a \<noteq> Some False" and
        rels_nv_cond: "\<not>volatile \<longrightarrow> (\<forall>j < length ts. i\<noteq>j \<longrightarrow> a \<notin> dom (released (ts!j)))"
	by cases auto

      from clean_no_outstanding_volatile_Write\<^sub>s\<^sub>b [OF i_bound ts\<^sub>s\<^sub>b_i] volatile_clean
      have volatile_cond: "volatile \<longrightarrow> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb ={}"
	by auto

      {
	fix j p\<^sub>j "is\<^sub>s\<^sub>b\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>s\<^sub>b\<^sub>j \<theta>\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j
	assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	assume neq_i_j: "i \<noteq> j"
	assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j, \<theta>\<^sub>s\<^sub>b\<^sub>j, sb\<^sub>j, \<D>\<^sub>s\<^sub>b\<^sub>j, \<O>\<^sub>j,\<R>\<^sub>j)"
	assume non_vol: "\<not> volatile"
	have "a \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	proof 
	  assume a_j: "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	  let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	  let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"


          from ts_sim [rule_format, OF j_bound] jth
	  obtain suspends\<^sub>j "is\<^sub>j" \<D>\<^sub>j where
	    suspends\<^sub>j: "suspends\<^sub>j = ?drop_sb\<^sub>j" and
	    is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
	    \<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
	    ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j, 
	    \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), 
	    \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	    by (auto simp add: Let_def)
	    

	  from a_j ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
	  have a_notin_sb: "a \<notin> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
	    by auto
	  with acquired_all_acquired [of True sb \<O>\<^sub>s\<^sub>b]
	  have a_not_acq: "a \<notin> acquired True sb \<O>\<^sub>s\<^sub>b" by blast
	  with access_cond' non_vol
	  have a_ro: "a \<in> read_only (share ?drop_sb \<S>)"
	    by auto
          from read_only_share_unowned_in [OF weak_consis_drop a_ro] a_notin_sb
            acquired_all_acquired [of True ?take_sb \<O>\<^sub>s\<^sub>b]
            all_acquired_append [of ?take_sb ?drop_sb]
          have a_ro_shared: "a \<in> read_only \<S>"
            by auto

          from rels_nv_cond [rule_format, OF non_vol j_bound [simplified leq] neq_i_j] ts\<^sub>j
          have "a \<notin> dom (release ?take_sb\<^sub>j (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>j)"
            by auto
          with dom_release_takeWhile [of sb\<^sub>j "(dom (\<S>\<^sub>s\<^sub>b))" \<R>\<^sub>j]
          obtain
            a_rels\<^sub>j: "a \<notin> dom \<R>\<^sub>j" and
            a_shared\<^sub>j: "a \<notin> all_shared ?take_sb\<^sub>j"
            by auto
          
          
          have "a \<notin> \<Union>((\<lambda>(_, _, _, sb, _, _, _). all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) `
                 set ts\<^sub>s\<^sub>b)"
          proof -
            {
              fix k p\<^sub>k "is\<^sub>k" \<theta>\<^sub>k sb\<^sub>k \<D>\<^sub>k \<O>\<^sub>k \<R>\<^sub>k 
              assume k_bound: "k < length ts\<^sub>s\<^sub>b" 
              assume ts_k: "ts\<^sub>s\<^sub>b ! k = (p\<^sub>k,is\<^sub>k,\<theta>\<^sub>k,sb\<^sub>k,\<D>\<^sub>k,\<O>\<^sub>k,\<R>\<^sub>k)" 
              assume a_in: "a \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k)"
              have False
              proof (cases "k=j")
                case True with a_shared\<^sub>j jth ts_k a_in show False by auto
              next
                case False
                from ownership_distinct [OF j_bound k_bound False [symmetric] jth ts_k] a_j
                have "a \<notin> (\<O>\<^sub>k \<union> all_acquired sb\<^sub>k)" by auto
                with all_shared_acquired_or_owned [OF sharing_consis [OF k_bound ts_k]] a_in
                show False 
                using all_acquired_append [of "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k" 
                  "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k"] 
                  all_shared_append [of "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k" 
                  "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k"] by auto 
              qed
            }
            thus ?thesis by (fastforce simp add: in_set_conv_nth)
          qed
          with a_ro_shared
            read_only_shared_all_until_volatile_write_subset' [of ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b]
          have a_ro_shared\<^sub>s\<^sub>b: "a \<in> read_only \<S>\<^sub>s\<^sub>b"
            by (auto simp add: \<S>)
          
	  with read_only_unowned [OF j_bound jth]
	  have a_notin_owns_j: "a \<notin> \<O>\<^sub>j"
	    by auto


	  have own_dist: "ownership_distinct ts\<^sub>s\<^sub>b" by fact
	  have share_consis: "sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b" by fact
	  from sharing_consistent_share_all_until_volatile_write [OF own_dist share_consis i_bound ts\<^sub>s\<^sub>b_i]
	  have consis': "sharing_consistent \<S> (acquired True ?take_sb \<O>\<^sub>s\<^sub>b) ?drop_sb"
	    by (simp add: \<S>)
          from  share_all_until_volatile_write_thread_local [OF own_dist share_consis j_bound jth a_j] a_ro_shared
          have a_ro_take: "a \<in> read_only (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
            by (auto simp add: domIff \<S> read_only_def)
          from sharing_consis [OF j_bound jth]
          have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
          from sharing_consistent_weak_sharing_consistent [OF this] weak_sharing_consistent_append [of \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
          have weak_consis_drop:"weak_sharing_consistent \<O>\<^sub>j ?take_sb\<^sub>j"
            by auto
          from read_only_share_acquired_all_shared [OF this read_only_unowned [OF j_bound jth] a_ro_take ] a_notin_owns_j a_shared\<^sub>j
          have "a \<notin> all_acquired ?take_sb\<^sub>j"
            by auto
	  with a_j a_notin_owns_j
	  have a_drop: "a \<in> all_acquired ?drop_sb\<^sub>j"
	    using all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	    by simp
	  

	  from i_bound j_bound leq have j_bound_ts': "j < length ?ts'"
	    by auto

	  note conflict_drop = a_drop [simplified suspends\<^sub>j [symmetric]]
	  from split_all_acquired_in [OF conflict_drop]
	    (* FIXME: exract common parts *)
	  show False
	  proof 
	    assume "\<exists>sop a' v ys zs A L R W. 
              (suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W# zs) \<and> a \<in> A"
	    then 
	    obtain a' sop' v' ys zs A' L' R' W' where
	      split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# zs" 
	      (is "suspends\<^sub>j = ?suspends") and
		a_A': "a \<in> A'"
	      by blast

	    from sharing_consis [OF j_bound jth]
	    have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	    then have A'_R': "A' \<inter> R' = {}" 
	      by (simp add: sharing_consistent_append [of _ _ ?take_sb\<^sub>j ?drop_sb\<^sub>j, simplified] 
		suspends\<^sub>j [symmetric] split_suspends\<^sub>j sharing_consistent_append)
	    from valid_program_history [OF j_bound jth] 
	    have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	    then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
	      apply -
	      apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply (simp add: split_suspends\<^sub>j)
	      done

	    from ts\<^sub>j neq_i_j j_bound 
	    have ts'_j: "?ts'!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
	      \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), 
	      \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j, release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	      by auto
	    from valid_last_prog [OF j_bound jth] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	    then
	    have lp: "last_prog p\<^sub>j suspends\<^sub>j = p\<^sub>j"
	      apply -
	      apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done
	    from valid_reads [OF j_bound jth]
	    have reads_consis_j: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	    from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> j_bound 
	      jth reads_consis_j]
	    have reads_consis_m_j: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
	      by (simp add: m suspends\<^sub>j)


	    from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
	    have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
	      by (simp add: suspends\<^sub>j)
	    from reads_consistent_flush_independent [OF this reads_consis_m_j]
	    have reads_consis_flush_suspend: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
	      (flush ?drop_sb m) suspends\<^sub>j".
	    hence reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
	      (flush ?drop_sb m) (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'])"
	      by (simp add: split_suspends\<^sub>j reads_consistent_append)

	    from valid_write_sops [OF j_bound jth]
	    have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
	      valid_sops_drop: "\<forall>sop\<in>write_sops (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']). valid_sop sop"
	      apply (simp only: write_sops_append)
	      apply auto
	      done

	    from read_tmps_distinct [OF j_bound jth]
	    have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    then obtain 
	      read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
	      distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      apply (simp only: distinct_read_tmps_append)
	      done

	    from valid_history [OF j_bound jth]
	    have h_consis: 
	      "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done
	    
	    have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	    proof -
	      from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		by simp
	      from last_prog_hd_prog_append' [OF h_consis] this
	      have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      moreover 
	      have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		by (rule last_prog_hd_prog_append)
	      ultimately show ?thesis
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	    qed

	    from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
	      h_consis] last_prog_hd_prog
	    have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    from reads_consistent_drop_volatile_writes_no_volatile_reads  
	    [OF reads_consis_j] 
	    have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b 
	      (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) = {}"
	      by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		split_suspends\<^sub>j )

	    have acq_simp:
	      "acquired True (ys @ [Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) 
              (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) = 
              acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R'"
	      by (simp add: acquired_append)

	    from flush_store_buffer_append [where sb="ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']" and sb'="zs", simplified,
	      OF j_bound_ts' is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
	      ts'_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_ys 
	      hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
	      distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
	      no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
	      \<S>="share ?drop_sb \<S>"]

	    obtain is\<^sub>j' \<R>\<^sub>j' where
	      is\<^sub>j': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs" and
	      steps_ys: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>)  \<Rightarrow>\<^sub>d\<^sup>* 
	      (?ts'[j:=(last_prog
              (hd_prog p\<^sub>j (Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# zs)) (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']),
              is\<^sub>j',
              \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps zs),
              (), True, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R',\<R>\<^sub>j')],
              flush (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) (flush ?drop_sb m),
              share (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) (share ?drop_sb \<S>))"
	      (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
              by (auto simp add: acquired_append outstanding_refs_append)

	    from i_bound' have i_bound_ys: "i < length ?ts_ys"
	      by auto

	    from i_bound' neq_i_j 
	    have ts_ys_i: "?ts_ys!i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b,(), 
	      \<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b, release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
	      by simp
	    note conflict_computation = rtranclp_trans [OF steps_flush_sb steps_ys]
	    
	    from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	    have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	    
	    from safe_delayedE [OF this i_bound_ys ts_ys_i, simplified is\<^sub>s\<^sub>b] non_vol a_not_acq
	    have "a \<in> read_only (share (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) (share ?drop_sb \<S>))"
	      apply cases
	      apply (auto simp add: Let_def is\<^sub>s\<^sub>b)
	      done

	    with a_A'
	    show False
	      by (simp add: share_append in_read_only_convs)
	  next
	    assume "\<exists>A L R W ys zs. suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A L R W # zs \<and> a \<in> A"
	    then 
	    obtain A' L' R' W' ys zs where
	      split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs" 
	      (is "suspends\<^sub>j = ?suspends") and
		a_A': "a \<in> A'"
	      by blast

	    from valid_program_history [OF j_bound jth] 
	    have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	    then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
	      apply -
	      apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply (simp add: split_suspends\<^sub>j)
	      done

	    from ts\<^sub>j neq_i_j j_bound 
	    have ts'_j: "?ts'!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
	      \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), 
	      \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j, release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	      by auto
	    from valid_last_prog [OF j_bound jth] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	    then
	    have lp: "last_prog p\<^sub>j suspends\<^sub>j = p\<^sub>j"
	      apply -
	      apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done


	    from valid_reads [OF j_bound jth]
	    have reads_consis_j: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	    from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> j_bound 
	      jth reads_consis_j]
	    have reads_consis_m_j: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
	      by (simp add: m suspends\<^sub>j)

	    from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
	    have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
	      by (simp add: suspends\<^sub>j)
	    from reads_consistent_flush_independent [OF this reads_consis_m_j]
	    have reads_consis_flush_suspend: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
	      (flush ?drop_sb m) suspends\<^sub>j".

	    hence reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)  
	      (flush ?drop_sb m) (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W'])"
	      by (simp add: split_suspends\<^sub>j reads_consistent_append)
	    from valid_write_sops [OF j_bound jth]
	    have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
	      valid_sops_drop: "\<forall>sop\<in>write_sops (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']). valid_sop sop"
	      apply (simp only: write_sops_append)
	      apply auto
	      done

	    from read_tmps_distinct [OF j_bound jth]
	    have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    then obtain 
	      read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
	      distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      apply (simp only: distinct_read_tmps_append)
	      done

	    from valid_history [OF j_bound jth]
	    have h_consis: 
	      "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done
	    
	    have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	    proof -
	      from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		by simp
	      from last_prog_hd_prog_append' [OF h_consis] this
	      have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      moreover 
	      have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		by (rule last_prog_hd_prog_append)
	      ultimately show ?thesis
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	    qed

	    from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
	      h_consis] last_prog_hd_prog
	    have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    from reads_consistent_drop_volatile_writes_no_volatile_reads  
	    [OF reads_consis_j] 
	    have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b 
	      (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) = {}"
	      by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		split_suspends\<^sub>j )

	    have acq_simp:
	      "acquired True (ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W']) 
              (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) = 
              acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R'"
	      by (simp add: acquired_append)

	    from flush_store_buffer_append [where sb="ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']" and sb'="zs", simplified,
	      OF j_bound_ts' is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
	      ts'_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_ys 
	      hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
	      distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
	      no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
	      \<S>="share ?drop_sb \<S>"]
	    obtain is\<^sub>j' \<R>\<^sub>j' where
	      is\<^sub>j': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs" and
	      steps_ys: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>)  \<Rightarrow>\<^sub>d\<^sup>* 
	      (?ts'[j:=(last_prog
              (hd_prog p\<^sub>j (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)) (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']),
              is\<^sub>j',
              \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps zs),
              (),
              \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W']) \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R',\<R>\<^sub>j')],
              flush (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) (flush ?drop_sb m),
              share (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) (share ?drop_sb \<S>))"
	      (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
              by (auto simp add: acquired_append)

	    from i_bound' have i_bound_ys: "i < length ?ts_ys"
	      by auto

	    from i_bound' neq_i_j 
	    have ts_ys_i: "?ts_ys!i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b,\<theta>\<^sub>s\<^sub>b,(), 
	      \<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b, release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
	      by simp
	    note conflict_computation = rtranclp_trans [OF steps_flush_sb steps_ys]
	    
	    from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	    have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	    
	    from safe_delayedE [OF this i_bound_ys ts_ys_i, simplified is\<^sub>s\<^sub>b] non_vol a_not_acq
	    have "a \<in> read_only (share (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) (share ?drop_sb \<S>))"
	      apply cases
	      apply (auto simp add: Let_def is\<^sub>s\<^sub>b)
	      done

	    with a_A'
	    show False
	      by (simp add: share_append in_read_only_convs)
	  qed
	qed
      }
      note non_volatile_unowned_others = this

            {
        assume a_in: "a \<in> read_only (share (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>)"
        assume nv: "\<not> volatile"
        have "a \<in> read_only (share sb \<S>\<^sub>s\<^sub>b)"
        proof (cases "a \<in> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb")
          case True
          from share_all_until_volatile_write_thread_local' [OF ownership_distinct_ts\<^sub>s\<^sub>b 
            sharing_consis_ts\<^sub>s\<^sub>b i_bound ts\<^sub>s\<^sub>b_i True] True a_in
          show ?thesis
            by (simp add: \<S> read_only_def)
        next
          case False
          from read_only_share_unowned [OF weak_consis_drop _ a_in] False 
            acquired_all_acquired [of True ?take_sb \<O>\<^sub>s\<^sub>b] all_acquired_append [of ?take_sb ?drop_sb]
          have a_ro_shared: "a \<in> read_only \<S>"
            by auto
          have "a \<notin> \<Union>((\<lambda>(_, _, _, sb, _, _, _).
               all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts\<^sub>s\<^sub>b)"
          proof -
            {
              fix k p\<^sub>k "is\<^sub>k" \<theta>\<^sub>k sb\<^sub>k \<D>\<^sub>k \<O>\<^sub>k \<R>\<^sub>k 
              assume k_bound: "k < length ts\<^sub>s\<^sub>b" 
              assume ts_k: "ts\<^sub>s\<^sub>b ! k = (p\<^sub>k,is\<^sub>k,\<theta>\<^sub>k,sb\<^sub>k,\<D>\<^sub>k,\<O>\<^sub>k,\<R>\<^sub>k)" 
              assume a_in: "a \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k)"
              have False
              proof (cases "k=i")
                case True with False ts\<^sub>s\<^sub>b_i ts_k a_in 
                  all_shared_acquired_or_owned [OF sharing_consis [OF k_bound ts_k]]     
                  all_shared_append [of "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k" 
                  "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k"] show False by auto
              next
                case False
                from rels_nv_cond [rule_format, OF nv k_bound [simplified leq] False [symmetric] ] 
                ts_sim [rule_format, OF k_bound] ts_k
                have "a \<notin> dom (release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k) (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>k)"
                  by (auto simp add: Let_def)
                with dom_release_takeWhile [of sb\<^sub>k "(dom (\<S>\<^sub>s\<^sub>b))" \<R>\<^sub>k]
                obtain
                  a_rels\<^sub>j: "a \<notin> dom \<R>\<^sub>k" and
                  a_shared\<^sub>j: "a \<notin> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>k)"
                  by auto
                with False a_in show ?thesis 
                  by auto
             qed
           }      
           thus ?thesis 
             by (auto simp add: in_set_conv_nth)
          qed
          with read_only_shared_all_until_volatile_write_subset' [of ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b] a_ro_shared
          have "a \<in> read_only \<S>\<^sub>s\<^sub>b"
            by (auto simp add: \<S>)

          from read_only_share_unowned' [OF weak_consis_sb read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] False  this]
          show ?thesis .
        qed
      } note non_vol_ro_reduction = this

      have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof (cases volatile)
	  case False
	  from outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i]
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb".
	  then

	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb@[Read\<^sub>s\<^sub>b False a t (m\<^sub>s\<^sub>b a)])"
	    using access_cond' False non_vol_ro_reduction
	    by (auto simp add: non_volatile_owned_or_read_only_append)

	  from outstanding_non_volatile_refs_owned_or_read_only_nth_update [OF i_bound this]
	  show ?thesis by (auto simp add: False ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	next
	  case True
	  from outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i]  
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb".
	  then
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb@[Read\<^sub>s\<^sub>b True a t (m\<^sub>s\<^sub>b a)])"
	    using True
	    by (simp add: non_volatile_owned_or_read_only_append)
	  from outstanding_non_volatile_refs_owned_or_read_only_nth_update [OF i_bound this]
	  show ?thesis by (auto simp add: True ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	qed
      next
	show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'"
	proof -
	  have out: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)]) \<subseteq> 
            outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb"
	    by (auto simp add: outstanding_refs_append)
	  have "all_acquired (sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)]) \<subseteq> all_acquired sb"
	    by (auto simp add: all_acquired_append)
	  from outstanding_volatile_writes_unowned_by_others_store_buffer 
	  [OF i_bound ts\<^sub>s\<^sub>b_i out this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b')
	qed
      next
	show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
	proof (cases volatile)
	  case True
	  have r: "read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) 
	            (sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)])) \<O>\<^sub>s\<^sub>b)
                    (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)]))
                \<subseteq> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>\<^sub>s\<^sub>b)
                    (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
	    apply (case_tac "outstanding_refs (is_volatile_Write\<^sub>s\<^sub>b) sb = {}")
	    apply (simp_all add: outstanding_vol_write_take_drop_appends
	    acquired_append read_only_reads_append True)
	    done

	  have "\<O>\<^sub>s\<^sub>b \<union> all_acquired (sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)]) \<subseteq> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
	    by (simp add: all_acquired_append)

	 
	  from  read_only_reads_unowned_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i r this]
	  show ?thesis
	    by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb')
	next
	  case False
	  show ?thesis
	  proof (unfold_locales)
	    fix n m
	    fix p\<^sub>n "is\<^sub>n" \<O>\<^sub>n \<R>\<^sub>n \<D>\<^sub>n \<theta>\<^sub>n sb\<^sub>n p\<^sub>m "is\<^sub>m" \<O>\<^sub>m \<R>\<^sub>m \<D>\<^sub>m \<theta>\<^sub>m sb\<^sub>m
	    assume n_bound: "n < length ts\<^sub>s\<^sub>b'"
	    and m_bound: "m < length ts\<^sub>s\<^sub>b'"
	    and neq_n_m: "n\<noteq>m"
	    and nth: "ts\<^sub>s\<^sub>b'!n = (p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
	    and mth: "ts\<^sub>s\<^sub>b'!m =(p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m,\<R>\<^sub>m)"
	    from n_bound have n_bound': "n < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')
	    from m_bound have m_bound': "m < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')

	    have acq_eq: "(\<O>\<^sub>s\<^sub>b' \<union> all_acquired sb') = (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb)"
	      by (simp add: all_acquired_append sb' \<O>\<^sub>s\<^sub>b')	      

	    show "(\<O>\<^sub>m \<union> all_acquired sb\<^sub>m) \<inter>
              read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) \<O>\<^sub>n)
              (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) =
              {}"
	    proof (cases "m=i")
	      case True
	      with neq_n_m have neq_n_i: "n\<noteq>i"
		by auto
		
	      with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      note read_only_reads_unowned [OF n_bound' i_bound  neq_n_i nth' ts\<^sub>s\<^sub>b_i]
	      moreover
	      note acq_eq
	      ultimately show ?thesis
		using True ts\<^sub>s\<^sub>b_i nth mth n_bound' m_bound'
		by (simp add: ts\<^sub>s\<^sub>b')
	    next
	      case False
	      note neq_m_i = this
	      with m_bound mth i_bound have mth': "ts\<^sub>s\<^sub>b!m = (p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m,\<R>\<^sub>m)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      show ?thesis
	      proof (cases "n=i")
		case True
		note read_only_reads_unowned [OF i_bound m_bound' neq_m_i [symmetric] ts\<^sub>s\<^sub>b_i mth']
		moreover 
		note acq_eq
		moreover
		note non_volatile_unowned_others [OF m_bound' neq_m_i [symmetric] mth']
		ultimately show ?thesis
		  using True ts\<^sub>s\<^sub>b_i nth mth n_bound' m_bound' neq_m_i
		  apply (case_tac "outstanding_refs (is_volatile_Write\<^sub>s\<^sub>b) sb = {}")
		  apply (clarsimp simp add: outstanding_vol_write_take_drop_appends
		    acquired_append read_only_reads_append ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b')+
		  done
	      next
		case False
		with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
		  by (auto simp add: ts\<^sub>s\<^sub>b')
		from read_only_reads_unowned [OF n_bound' m_bound' neq_n_m  nth' mth'] False neq_m_i
		show ?thesis 
		  by (clarsimp)
	      qed
	    qed
	  qed
	qed
	show "ownership_distinct ts\<^sub>s\<^sub>b'"
	proof -
	  have "all_acquired (sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)]) \<subseteq> all_acquired sb"
	    by (auto simp add: all_acquired_append)
	  from ownership_distinct_instructions_read_value_store_buffer_independent 
	  [OF i_bound ts\<^sub>s\<^sub>b_i this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b')
	qed
      qed


      have valid_hist': "valid_history program_step ts\<^sub>s\<^sub>b'"
      proof -
	from valid_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have hcons: "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b sb) sb".
	from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have t_notin_reads: "t \<notin> read_tmps sb"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	from load_tmps_write_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have t_notin_writes: "t \<notin> \<Union>(fst ` write_sops sb )"
	  by (auto simp add: "is\<^sub>s\<^sub>b")

	from valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	have valid_sops: "\<forall>sop \<in> write_sops sb. valid_sop sop"
	  by auto
	from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i]
	have t_fresh: "t \<notin> dom \<theta>\<^sub>s\<^sub>b"
	  using "is\<^sub>s\<^sub>b"
	  by simp

	from valid_implies_valid_prog_hd [OF i_bound ts\<^sub>s\<^sub>b_i valid]
	have "history_consistent (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m\<^sub>s\<^sub>b a)) 
	       (hd_prog p\<^sub>s\<^sub>b (sb@ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)])) 
               (sb@ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)])"
	  using t_notin_writes valid_sops t_fresh hcons
	  apply -
	  apply (rule history_consistent_appendI)
	  apply (auto simp add: hd_prog_append_Read\<^sub>s\<^sub>b)
	  done

	from valid_history_nth_update [OF i_bound this]
	show ?thesis
	  by (auto simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
      qed

      from 
	reads_consistent_unbuffered_snoc [OF buf_None refl valid_reads [OF i_bound ts\<^sub>s\<^sub>b_i] volatile_cond ]    
      have reads_consis': "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b (sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)])"
	by (simp split: if_split_asm)

      from valid_reads_nth_update [OF i_bound this]
      have valid_reads': "valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b')

      have valid_sharing': "valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)	
	from outstanding_non_volatile_writes_unshared [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b (sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)])"
	  by (auto simp add: non_volatile_writes_unshared_append)
	from outstanding_non_volatile_writes_unshared_nth_update [OF i_bound this]
	show "outstanding_non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' sb' \<S>\<^sub>s\<^sub>b')
      next
	from sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb".
	then
	have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)])"
	  by (simp add:  sharing_consistent_append)
	from sharing_consis_nth_update [OF i_bound this]
	show "sharing_consis \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' \<S>\<^sub>s\<^sub>b')
      next
	note read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i]
	from read_only_unowned_nth_update [OF i_bound this]
	show "read_only_unowned \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b')
      next
	from unowned_shared_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i subset_refl]
	show "unowned_shared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next
	from no_outstanding_write_to_read_only_memory [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b sb".
	hence "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b (sb@[Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)])"
	  by (simp add: no_write_to_read_only_memory_append)
	from no_outstanding_write_to_read_only_memory_nth_update [OF i_bound this]
	show "no_outstanding_write_to_read_only_memory \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' sb')
      qed

      have tmps_distinct': "tmps_distinct ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_load_tmps is\<^sub>s\<^sub>b'"
	  by (auto split: instr.splits simp add: is\<^sub>s\<^sub>b)
	from load_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b')
      next
	from read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_read_tmps sb".
	moreover
	from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "t \<notin> read_tmps sb"
	  by (auto simp add: is\<^sub>s\<^sub>b)
	ultimately have "distinct_read_tmps (sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)])"
	  by (auto simp add: distinct_read_tmps_append)
	from read_tmps_distinct_nth_update [OF i_bound this]
	show "read_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb')
      next
	from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] 
          load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> read_tmps (sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)]) = {}"
	  by (clarsimp simp add: read_tmps_append "is\<^sub>s\<^sub>b")
	from load_tmps_read_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_read_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      have valid_sops': "valid_sops ts\<^sub>s\<^sub>b'"
      proof -
	from valid_store_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	have valid_store_sops': "\<forall>sop\<in>store_sops is\<^sub>s\<^sub>b'. valid_sop sop"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	from valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	have valid_write_sops': "\<forall>sop\<in>write_sops (sb@ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)]). 
	      valid_sop sop"
	  by (auto simp add: write_sops_append)
	from valid_sops_nth_update [OF i_bound  valid_write_sops' valid_store_sops']
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      have valid_dd': "valid_data_dependency ts\<^sub>s\<^sub>b'"
      proof -
	from data_dependency_consistent_instrs [OF i_bound ts\<^sub>s\<^sub>b_i]
	have dd_is: "data_dependency_consistent_instrs (dom \<theta>\<^sub>s\<^sub>b') is\<^sub>s\<^sub>b'"
	  by (auto simp add: "is\<^sub>s\<^sub>b" \<theta>\<^sub>s\<^sub>b')
	from load_tmps_write_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> \<Union>(fst ` write_sops (sb@ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)])) = {}"
	  by (auto simp add: write_sops_append "is\<^sub>s\<^sub>b")
	from valid_data_dependency_nth_update [OF i_bound dd_is this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      have load_tmps_fresh': "load_tmps_fresh ts\<^sub>s\<^sub>b'"
      proof -
	from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "load_tmps (Read volatile a t # is\<^sub>s\<^sub>b') \<inter> dom \<theta>\<^sub>s\<^sub>b = {}"
	  by (simp add: "is\<^sub>s\<^sub>b")
	moreover
	from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] have "t \<notin> load_tmps is\<^sub>s\<^sub>b'"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	ultimately have "load_tmps is\<^sub>s\<^sub>b' \<inter> dom (\<theta>\<^sub>s\<^sub>b(t \<mapsto> (m\<^sub>s\<^sub>b a))) = {}"
	  by auto
	from load_tmps_fresh_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<theta>\<^sub>s\<^sub>b')
      qed

      have enough_flushs': "enough_flushs ts\<^sub>s\<^sub>b'"
      proof -
	from clean_no_outstanding_volatile_Write\<^sub>s\<^sub>b [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "\<not> \<D>\<^sub>s\<^sub>b \<longrightarrow> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)]) = {}"
	  by (auto simp add: outstanding_refs_append )
	from enough_flushs_nth_update [OF i_bound this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' sb' \<D>\<^sub>s\<^sub>b')
      qed

      have valid_program_history': "valid_program_history ts\<^sub>s\<^sub>b'"
      proof -	
	from valid_program_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "causal_program_history is\<^sub>s\<^sub>b sb" .
	then have causal': "causal_program_history is\<^sub>s\<^sub>b' (sb@[Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)])"
	  by (auto simp: causal_program_history_Read  "is\<^sub>s\<^sub>b")
	from valid_last_prog [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "last_prog p\<^sub>s\<^sub>b sb = p\<^sub>s\<^sub>b".
	hence "last_prog p\<^sub>s\<^sub>b (sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)]) = p\<^sub>s\<^sub>b"
	  by (simp add: last_prog_append_Read\<^sub>s\<^sub>b)
	from valid_program_history_nth_update [OF i_bound causal' this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      show ?thesis
      proof (cases "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}")
	case True 

	from True have flush_all: "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = sb"
	  by (auto simp add: outstanding_refs_conv )

	from True have suspend_nothing: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = []"
	  by (auto simp add: outstanding_refs_conv)

	hence suspends_empty: "suspends = []"
	  by (simp add: suspends)
	from suspends_empty is_sim have "is": "is = Read volatile a t # is\<^sub>s\<^sub>b'"
	  by (simp add: "is\<^sub>s\<^sub>b")
	with suspends_empty ts_i 
	have ts_i: "ts!i = (p\<^sub>s\<^sub>b, Read volatile a t # is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b,(), 
          \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b, release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
	  by simp

	from direct_memop_step.Read
	have "(Read volatile a t # is\<^sub>s\<^sub>b',\<theta>\<^sub>s\<^sub>b, (), m, 
            \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b,\<S>) \<rightarrow> 
          (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t \<mapsto> m a), (), m, \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,
           release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b, \<S>)".
	from direct_computation.concurrent_step.Memop [OF i_bound' ts_i this]
	have "(ts, m, \<S>) \<Rightarrow>\<^sub>d (ts[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t \<mapsto> m a), (), 
	   \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)], m, \<S>)".

	moreover
	
	from flush_all_until_volatile_write_Read_commute [OF i_bound ts\<^sub>s\<^sub>b_i [simplified "is\<^sub>s\<^sub>b"] ]
	have flush_commute: "flush_all_until_volatile_write
          (ts\<^sub>s\<^sub>b[i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t\<mapsto>m\<^sub>s\<^sub>b a), sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)], \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b)]) 
           m\<^sub>s\<^sub>b =
          flush_all_until_volatile_write ts\<^sub>s\<^sub>b m\<^sub>s\<^sub>b".
	
	have "flush_all_until_volatile_write ts\<^sub>s\<^sub>b m\<^sub>s\<^sub>b a = m\<^sub>s\<^sub>b a"
	proof -
          have "\<forall>j < length ts\<^sub>s\<^sub>b. i \<noteq> j \<longrightarrow>
                  (let (_,_,_,sb\<^sub>j,_,_,_) = ts\<^sub>s\<^sub>b!j 
                  in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))"
	  proof -
	    {
	      fix j p\<^sub>j "is\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j acq\<^sub>j xs\<^sub>j sb\<^sub>j
	      assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	      assume neq_i_j: "i \<noteq> j"
	      assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j, xs\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j, \<R>\<^sub>j)"
	      have "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	      proof 
		let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
		let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
		assume a_in: "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b ?take_sb\<^sub>j"
		with outstanding_refs_takeWhile [where P'= "Not \<circ> is_volatile_Write\<^sub>s\<^sub>b"]
		have a_in': "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
		  by auto
		with non_volatile_owned_or_read_only_outstanding_non_volatile_writes 
		[OF outstanding_non_volatile_refs_owned_or_read_only [OF j_bound jth]]
		have j_owns: "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
		  by auto
		with ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
		have a_not_owns: "a \<notin> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
		  by blast
		
		from non_volatile_owned_or_read_only_append [of False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		  outstanding_non_volatile_refs_owned_or_read_only [OF j_bound jth]
		have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j"
		  by simp
		from non_volatile_owned_or_read_only_outstanding_non_volatile_writes [OF this] a_in
		have j_owns_drop: "a \<in> \<O>\<^sub>j \<union> all_acquired ?take_sb\<^sub>j"
		  by auto
		
                from rels_cond [rule_format, OF j_bound [simplified leq] neq_i_j] ts_sim [rule_format, OF j_bound] jth
                have no_unsharing:"release ?take_sb\<^sub>j (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>j  a \<noteq> Some False"
                  by (auto simp add: Let_def)
		{
		  assume "a \<in> acquired True sb \<O>\<^sub>s\<^sub>b"
		  with acquired_all_acquired_in [OF this] ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth] 
		    j_owns 
		  have False
		    by auto
		}
		moreover
		{
		  assume a_ro: "a \<in> read_only (share ?drop_sb \<S>)"
                  from read_only_share_unowned_in [OF weak_consis_drop a_ro] a_not_owns
                  acquired_all_acquired [of True ?take_sb \<O>\<^sub>s\<^sub>b]
                  all_acquired_append [of ?take_sb ?drop_sb]
                  have "a \<in> read_only \<S>"
                    by auto
                  with share_all_until_volatile_write_thread_local [OF ownership_distinct_ts\<^sub>s\<^sub>b sharing_consis_ts\<^sub>s\<^sub>b j_bound jth j_owns]
                  have "a \<in> read_only (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
                    by (auto simp add: read_only_def \<S>)
                  hence a_dom: "a \<in> dom  (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
                    by (auto simp add: read_only_def domIff)
                  from outstanding_non_volatile_writes_unshared [OF j_bound jth]
                  non_volatile_writes_unshared_append [of \<S>\<^sub>s\<^sub>b ?take_sb\<^sub>j ?drop_sb\<^sub>j]
                  have nvw: "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b ?take_sb\<^sub>j" by auto
                  from release_not_unshared_no_write_take [OF this no_unsharing a_dom] a_in
                  have False by auto
		}
		moreover
		{
		  assume a_share: "volatile \<and> a \<in> dom (share ?drop_sb \<S>)"
		  from outstanding_non_volatile_writes_unshared [OF j_bound jth]
		  have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b sb\<^sub>j".
		  with non_volatile_writes_unshared_append [of \<S>\<^sub>s\<^sub>b "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
		  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
		  have unshared_take: "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		    by clarsimp
		
		  from valid_own have own_dist: "ownership_distinct ts\<^sub>s\<^sub>b"
		    by (simp add: valid_ownership_def)
		  from valid_sharing have "sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b"
		    by (simp add: valid_sharing_def)
		  from sharing_consistent_share_all_until_volatile_write [OF own_dist this i_bound ts\<^sub>s\<^sub>b_i]
		  have sc: "sharing_consistent \<S> (acquired True ?take_sb \<O>\<^sub>s\<^sub>b) ?drop_sb"
		    by (simp add: \<S>)
		  from sharing_consistent_share_all_shared 
		  have "dom (share ?drop_sb \<S>) \<subseteq> dom \<S> \<union> all_shared ?drop_sb"
		    by auto
		  also from sharing_consistent_all_shared [OF sc]
		  have "\<dots> \<subseteq> dom \<S> \<union> acquired True ?take_sb \<O>\<^sub>s\<^sub>b" by auto
		  also from acquired_all_acquired all_acquired_takeWhile 
		  have "\<dots> \<subseteq> dom \<S> \<union> (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb)" by force
		  finally
		  have a_shared: "a \<in> dom \<S>"
		    using a_share a_not_owns
		    by auto

                  with share_all_until_volatile_write_thread_local [OF ownership_distinct_ts\<^sub>s\<^sub>b sharing_consis_ts\<^sub>s\<^sub>b j_bound jth j_owns]
                  have a_dom: "a \<in> dom  (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
                    by (auto simp add: \<S> domIff)
                  from release_not_unshared_no_write_take [OF  unshared_take no_unsharing a_dom] a_in
                  have False by auto
		}
		ultimately show False
		  using access_cond'
		  by auto
	      qed
	    }
	    thus ?thesis
	      by (fastforce simp add: Let_def)
	  qed
	  
	  from flush_all_until_volatile_write_buffered_val_conv 
	  [OF True i_bound ts\<^sub>s\<^sub>b_i this]
	  show ?thesis
	    by (simp add: buf_None)
	qed
	
	hence m_a: "m a = m\<^sub>s\<^sub>b a"
	  by (simp add: m)
	
	have tmps_commute: "\<theta>\<^sub>s\<^sub>b(t \<mapsto> (m\<^sub>s\<^sub>b a)) = 
	  (\<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b - {t}))(t \<mapsto> (m\<^sub>s\<^sub>b a))"
	  apply (rule ext)
	  apply (auto simp add: restrict_map_def domIff)
	  done

	from suspend_nothing
	have suspend_nothing': "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') = []"
	  by (simp add: sb')

	from \<D>
	have \<D>': "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)]) \<noteq>  {})"
	  by (auto simp: outstanding_refs_append)

	have "(ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> (ts[i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t\<mapsto>m a),(), \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)], m,\<S>)"
	  apply (rule sim_config.intros) 
	  apply    (simp add: m flush_commute ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb' \<D>\<^sub>s\<^sub>b' )
	  using   share_all_until_volatile_write_Read_commute [OF i_bound ts\<^sub>s\<^sub>b_i [simplified is\<^sub>s\<^sub>b]]
	  apply   (simp add: \<S> \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
	  using  leq
	  apply  (simp add: ts\<^sub>s\<^sub>b')
	  using i_bound i_bound' ts_sim ts_i True \<D>'
	  apply (clarsimp simp add: Let_def nth_list_update 
	    outstanding_refs_conv m_a  ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb' \<D>\<^sub>s\<^sub>b' suspend_nothing' 
	    flush_all acquired_append release_append
	    split: if_split_asm )
	  apply (rule tmps_commute)
	  done	

	ultimately show ?thesis
	  using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct'
	    valid_sops' valid_dd' load_tmps_fresh' enough_flushs' 
	    valid_program_history' valid'
	    m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' 
	  by (auto simp del: fun_upd_apply )
      next
	case False

	then obtain r where r_in: "r \<in> set sb" and volatile_r: "is_volatile_Write\<^sub>s\<^sub>b r"
	  by (auto simp add: outstanding_refs_conv)
	from takeWhile_dropWhile_real_prefix 
	[OF r_in, of  "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)", simplified, OF volatile_r] 
	obtain a' v' sb'' sop' A' L' R' W' where
	  sb_split: "sb = takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb @ Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# sb''" 
	  and
	  drop: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# sb''"
	  apply (auto)
    subgoal for y ys
	  apply (case_tac y)
	  apply auto
	  done
	  done
	from drop suspends have suspends: "suspends = Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# sb''"
	  by simp


	have "(ts, m, \<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts, m, \<S>)" by auto

	moreover

	note flush_commute = flush_all_until_volatile_write_Read_commute [OF i_bound ts\<^sub>s\<^sub>b_i 
	  [simplified "is\<^sub>s\<^sub>b"] ]

	have "Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'\<in> set sb"
	  by (subst sb_split) auto
	
	from dropWhile_append1 [OF this, of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)"]
	have drop_app_comm:
	  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)])) =
                dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb @ [Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)]"
	  by simp

	from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "t \<notin> dom \<theta>\<^sub>s\<^sub>b"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	then have tmps_commute: 
	  "\<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b - read_tmps sb'') =
          \<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b - insert t (read_tmps sb''))"
	  apply -
	  apply (rule ext)
	  apply auto
	  done

	from \<D>
	have \<D>': "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Read\<^sub>s\<^sub>b volatile a t (m\<^sub>s\<^sub>b a)]) \<noteq>  {})"
	  by (auto simp: outstanding_refs_append)

	have "(ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<sim> (ts,m,\<S>)"
	  apply (rule sim_config.intros) 
	  apply    (simp add: m flush_commute ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb')
	  using   share_all_until_volatile_write_Read_commute [OF i_bound ts\<^sub>s\<^sub>b_i [simplified is\<^sub>s\<^sub>b]]
	  apply   (simp add: \<S> \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
	  using  leq
	  apply  (simp add: ts\<^sub>s\<^sub>b')
	  using i_bound i_bound' ts_sim ts_i is_sim \<D>'
	  apply (clarsimp simp add: Let_def nth_list_update is_sim drop_app_comm 
	    read_tmps_append suspends prog_instrs_append_Read\<^sub>s\<^sub>b instrs_append_Read\<^sub>s\<^sub>b 
	    hd_prog_append_Read\<^sub>s\<^sub>b
	    drop "is\<^sub>s\<^sub>b" ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' \<D>\<^sub>s\<^sub>b' acquired_append takeWhile_append1 [OF r_in] volatile_r  split: if_split_asm)
	  apply (simp add: drop tmps_commute)+
	  done

	ultimately show ?thesis
	  using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' valid_dd'
	    valid_sops' load_tmps_fresh' enough_flushs' 
	    valid_program_history' valid'
	    m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' 
	  by (auto simp del: fun_upd_apply )
      qed
    next
      case (SBHWriteNonVolatile a D f A L R W)
      then obtain 
	"is\<^sub>s\<^sub>b": "is\<^sub>s\<^sub>b = Write False a (D, f) A L R W# is\<^sub>s\<^sub>b'" and
	\<O>\<^sub>s\<^sub>b': "\<O>\<^sub>s\<^sub>b'=\<O>\<^sub>s\<^sub>b" and
        \<R>\<^sub>s\<^sub>b': "\<R>\<^sub>s\<^sub>b'=\<R>\<^sub>s\<^sub>b" and
	\<theta>\<^sub>s\<^sub>b': "\<theta>\<^sub>s\<^sub>b' = \<theta>\<^sub>s\<^sub>b" and
	\<D>\<^sub>s\<^sub>b': "\<D>\<^sub>s\<^sub>b'=\<D>\<^sub>s\<^sub>b" and
	sb': "sb'=sb@[Write\<^sub>s\<^sub>b False a (D, f) (f \<theta>\<^sub>s\<^sub>b) A L R W]" and
	m\<^sub>s\<^sub>b': "m\<^sub>s\<^sub>b' = m\<^sub>s\<^sub>b" and
	\<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'=\<S>\<^sub>s\<^sub>b" 
	by auto


      from data_dependency_consistent_instrs [OF i_bound ts\<^sub>s\<^sub>b_i]
      have D_tmps: "D \<subseteq> dom \<theta>\<^sub>s\<^sub>b" 
	by (simp add: is\<^sub>s\<^sub>b)

      from safe_memop_flush_sb [simplified is\<^sub>s\<^sub>b]
      obtain a_owned': "a \<in> acquired True sb \<O>\<^sub>s\<^sub>b" and a_unshared': "a \<notin> dom (share ?drop_sb \<S>)" and
        rels_cond: "\<forall>j < length ts. i\<noteq>j \<longrightarrow> a \<notin> dom (released (ts!j))"
      (* FIXME: rels_cond unused; maybe remove from safe_delayed *) 
	by cases auto

      from a_owned' acquired_all_acquired
      have a_owned'': "a \<in> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
	by auto


      {
	fix j
	fix p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j
	assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	assume ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	assume neq_i_j: "i \<noteq> j"
	have "a \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	proof -
	  from ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j] a_owned''
	  show ?thesis
	    by auto
	qed
      } note a_unowned_others = this
	  
	    
      have a_unshared: "a \<notin> dom (share sb \<S>\<^sub>s\<^sub>b)"
      proof 
	assume a_share: "a \<in> dom (share sb \<S>\<^sub>s\<^sub>b)"
	from valid_sharing have "sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b"
	  by (simp add: valid_sharing_def)
	from in_shared_sb_share_all_until_volatile_write [OF this i_bound ts\<^sub>s\<^sub>b_i a_owned'' a_share]
	have "a \<in> dom (share ?drop_sb \<S>)"
	  by (simp add: \<S>)
	with a_unshared'
	show False
	  by auto
      qed

(*
      from acquired_owns_shared [OF sharing_consis_drop_sb]
      have "acquired True ?drop_sb \<O> \<subseteq> \<O> \<union> \<S>".
      moreover
      from share_owns_shared [OF sharing_consis_drop_sb]
      have "share ?drop_sb \<S> \<subseteq> \<O> \<union> \<S>".
*)
(*
      obtain a_owned: "a \<in> \<O>" and a_unshared: "a \<notin> \<S>" 
	by cases auto
*)
      have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof -
	  from outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i]  
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb".
	  
	  with a_owned' 
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])"
	    by (simp add: non_volatile_owned_or_read_only_append)
	  from outstanding_non_volatile_refs_owned_or_read_only_nth_update [OF i_bound this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b" sb' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	qed
      next
	show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'"
	proof -
	  have "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W]) \<subseteq> 
	    outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb"
	    by (auto simp add: outstanding_refs_append)
	  from outstanding_volatile_writes_unowned_by_others_store_buffer 
	  [OF i_bound ts\<^sub>s\<^sub>b_i this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b" sb' \<O>\<^sub>s\<^sub>b' all_acquired_append)
	qed
      next
	show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
	proof -
	  have r: "read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) 
	    (sb @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])) \<O>\<^sub>s\<^sub>b)
            (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W]))
            \<subseteq> 
	    read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>\<^sub>s\<^sub>b)
            (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
	    apply (case_tac "outstanding_refs (is_volatile_Write\<^sub>s\<^sub>b) sb = {}")
	    apply (simp_all add: outstanding_vol_write_take_drop_appends
	    acquired_append read_only_reads_append )
	    done
	  have "\<O>\<^sub>s\<^sub>b \<union> all_acquired (sb @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W]) \<subseteq> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
	    by (simp add: all_acquired_append)
	  

	  from read_only_reads_unowned_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i r this]
	  show ?thesis
	    by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb')
	qed 
      next
	show "ownership_distinct ts\<^sub>s\<^sub>b'"
	proof -
	  from ownership_distinct_instructions_read_value_store_buffer_independent 
	  [OF i_bound ts\<^sub>s\<^sub>b_i]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b" sb' \<O>\<^sub>s\<^sub>b' all_acquired_append)
	qed
      qed

      have valid_hist': "valid_history program_step ts\<^sub>s\<^sub>b'"
      proof -
	from valid_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b sb) sb".
	with valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i] D_tmps 
	  valid_implies_valid_prog_hd [OF i_bound ts\<^sub>s\<^sub>b_i valid]
	have "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b (sb@[Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])) 
	       (sb@ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])"
	  apply -
	  apply (rule history_consistent_appendI)
	  apply (auto simp add: hd_prog_append_Write\<^sub>s\<^sub>b)
	  done
	from valid_history_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b" sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
      qed

      have valid_reads': "valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b'"
      proof -
	from valid_reads [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b sb" .
	from reads_consistent_snoc_Write\<^sub>s\<^sub>b [OF this]
	have "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b (sb @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])".
	from valid_reads_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b" sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
      qed

      have valid_sharing': "valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)	
	from outstanding_non_volatile_writes_unshared [OF i_bound ts\<^sub>s\<^sub>b_i] a_unshared
	have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b
	      (sb @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])"
	  by (auto simp add: non_volatile_writes_unshared_append)
	from outstanding_non_volatile_writes_unshared_nth_update [OF i_bound this]
	show "outstanding_non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b" sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next
	from sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb".
	then
	have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])"
	  by (simp add:  sharing_consistent_append)
	from sharing_consis_nth_update [OF i_bound this]
	show "sharing_consis \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' \<S>\<^sub>s\<^sub>b')
      next
	from read_only_unowned_nth_update [OF i_bound read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] ]
	show "read_only_unowned \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b')
      next
	from unowned_shared_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i subset_refl]
	show "unowned_shared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b" sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next
	from a_unshared
	have "a \<notin> read_only (share sb \<S>\<^sub>s\<^sub>b)"
	  by (auto simp add: read_only_def dom_def)
	with no_outstanding_write_to_read_only_memory [OF i_bound ts\<^sub>s\<^sub>b_i] 

	have "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b (sb @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])"
	  by (simp add: no_write_to_read_only_memory_append)
	
	from no_outstanding_write_to_read_only_memory_nth_update [OF i_bound this]
	show "no_outstanding_write_to_read_only_memory \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb')
      qed

      have tmps_distinct': "tmps_distinct ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_load_tmps is\<^sub>s\<^sub>b'" 
	  by (auto split: instr.splits simp add: "is\<^sub>s\<^sub>b")
	from load_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_distinct ts\<^sub>s\<^sub>b'"	  
	  by (simp add: ts\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b" sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')      
      next
	from read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_read_tmps sb".
	hence "distinct_read_tmps (sb @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])" 
	  by (simp add: distinct_read_tmps_append)
	from read_tmps_distinct_nth_update [OF i_bound this]
	show "read_tmps_distinct ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b" sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')      
      next
	from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] 
          load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> read_tmps (sb @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W]) = {}"
	  by (clarsimp simp add: read_tmps_append "is\<^sub>s\<^sub>b")
	from load_tmps_read_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_read_tmps_distinct ts\<^sub>s\<^sub>b'" 
	  by (simp add: ts\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b" sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')      
      qed

      have valid_sops': "valid_sops ts\<^sub>s\<^sub>b'"
      proof -
	from valid_store_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	obtain valid_Df: "valid_sop (D,f)" and  
	  valid_store_sops': "\<forall>sop\<in>store_sops is\<^sub>s\<^sub>b'. valid_sop sop"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	from valid_Df valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	have valid_write_sops': "\<forall>sop\<in>write_sops (sb@ [Write\<^sub>s\<^sub>b False a (D, f) (f \<theta>\<^sub>s\<^sub>b) A L R W]). 
	  valid_sop sop"
	  by (auto simp add: write_sops_append)
	from valid_sops_nth_update [OF i_bound  valid_write_sops' valid_store_sops']
	show ?thesis 	  
	  by (simp add: ts\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b" sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')      
      qed

      have valid_dd': "valid_data_dependency ts\<^sub>s\<^sub>b'"
      proof -
	from data_dependency_consistent_instrs [OF i_bound ts\<^sub>s\<^sub>b_i]
	obtain D_indep: "D \<inter> load_tmps is\<^sub>s\<^sub>b' = {}" and 
	  dd_is: "data_dependency_consistent_instrs (dom \<theta>\<^sub>s\<^sub>b') is\<^sub>s\<^sub>b'"
	  by (auto simp add: "is\<^sub>s\<^sub>b" \<theta>\<^sub>s\<^sub>b')
	from load_tmps_write_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] D_indep
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> 
	      \<Union>(fst ` write_sops (sb@ [Write\<^sub>s\<^sub>b False a (D, f) (f \<theta>\<^sub>s\<^sub>b) A L R W])) = {}"
	  by (auto simp add: write_sops_append "is\<^sub>s\<^sub>b")
	from valid_data_dependency_nth_update [OF i_bound dd_is this]
	show ?thesis 	  
	  by (simp add: ts\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b" sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')      
      qed

      have load_tmps_fresh': "load_tmps_fresh ts\<^sub>s\<^sub>b'"
      proof -
	from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> dom \<theta>\<^sub>s\<^sub>b = {}"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	from load_tmps_fresh_nth_update [OF i_bound this]
	show ?thesis 	  
	  by (simp add: ts\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b" sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')      
      qed

      have enough_flushs': "enough_flushs ts\<^sub>s\<^sub>b'"
      proof -
	from clean_no_outstanding_volatile_Write\<^sub>s\<^sub>b [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "\<not> \<D>\<^sub>s\<^sub>b \<longrightarrow> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W]) = {}"
	  by (auto simp add: outstanding_refs_append )
	from enough_flushs_nth_update [OF i_bound this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' sb' \<D>\<^sub>s\<^sub>b')
      qed


      have valid_program_history': "valid_program_history ts\<^sub>s\<^sub>b'"
      proof -	
	from valid_program_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "causal_program_history is\<^sub>s\<^sub>b sb" .
	then have causal': "causal_program_history is\<^sub>s\<^sub>b' (sb@[Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])"
	  by (auto simp: causal_program_history_Write  "is\<^sub>s\<^sub>b")
	from valid_last_prog [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "last_prog p\<^sub>s\<^sub>b sb = p\<^sub>s\<^sub>b".
	hence "last_prog p\<^sub>s\<^sub>b (sb @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W]) = p\<^sub>s\<^sub>b"
	  by (simp add: last_prog_append_Write\<^sub>s\<^sub>b)
	from valid_program_history_nth_update [OF i_bound causal' this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed
      

      from valid_store_sops [OF i_bound ts\<^sub>s\<^sub>b_i, rule_format]
      have "valid_sop (D,f)" by (auto simp add: "is\<^sub>s\<^sub>b")
      then interpret valid_sop "(D,f)" .

      show ?thesis
      proof (cases "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}")
	case True
      
	from True have flush_all: "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = sb"
	  by (auto simp add: outstanding_refs_conv)
      
	from True have suspend_nothing: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = []"
	  by (auto simp add: outstanding_refs_conv)

	hence suspends_empty: "suspends = []"
	  by (simp add: suspends)

	from suspends_empty is_sim have "is": "is = Write False a (D,f) A L R W# is\<^sub>s\<^sub>b'"
	  by (simp add: "is\<^sub>s\<^sub>b")
	with suspends_empty ts_i 
	have ts_i: "ts!i = (p\<^sub>s\<^sub>b, Write False a (D,f) A L R W# is\<^sub>s\<^sub>b',
                     \<theta>\<^sub>s\<^sub>b,(),
                     \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,release ?take_sb (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>s\<^sub>b)"
	  by simp

	from direct_memop_step.WriteNonVolatile [OF ]
	have "(Write False a (D, f) A L R W# is\<^sub>s\<^sub>b', 
	  \<theta>\<^sub>s\<^sub>b, (),m,\<D>,acquired True ?take_sb \<O>\<^sub>s\<^sub>b ,release ?take_sb (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>s\<^sub>b, \<S>) \<rightarrow> 
               (is\<^sub>s\<^sub>b',
                  \<theta>\<^sub>s\<^sub>b, (), m(a := f \<theta>\<^sub>s\<^sub>b), \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,
                  release ?take_sb (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>s\<^sub>b, \<S>)".
	from direct_computation.concurrent_step.Memop [OF i_bound' ts_i this]
	have "(ts, m, \<S>) \<Rightarrow>\<^sub>d 
              (ts[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (),\<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,
                  release ?take_sb (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>s\<^sub>b)], 
	       m(a := f \<theta>\<^sub>s\<^sub>b),\<S>)".

	moreover


	have "\<forall>j<length ts\<^sub>s\<^sub>b. i \<noteq> j \<longrightarrow>
          (let (_,_, _, sb\<^sub>j,_,_,_) = ts\<^sub>s\<^sub>b ! j
          in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))"
	proof -
	  {
	    fix j p\<^sub>j "is\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j acq\<^sub>j xs\<^sub>j sb\<^sub>j
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	    assume neq_i_j: "i \<noteq> j"
	    assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j, xs\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j,\<R>\<^sub>j)"
	    have "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    proof 
	      assume a_in: "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	      hence "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
		using outstanding_refs_append [of is_non_volatile_Write\<^sub>s\<^sub>b "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
		"(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
		by auto
	      with non_volatile_owned_or_read_only_outstanding_non_volatile_writes 
	      [OF outstanding_non_volatile_refs_owned_or_read_only [OF j_bound jth]]
	      have j_owns: "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
		by auto

	      from j_owns a_owned'' ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
	      show False
		by auto
	    qed
	  }
	  thus ?thesis by (fastforce simp add: Let_def)
	qed

	note flush_commute = flush_all_until_volatile_write_append_non_volatile_write_commute
        [OF True i_bound ts\<^sub>s\<^sub>b_i this]

	from suspend_nothing
	have suspend_nothing': "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') = []"
	  by (simp add: sb')

	from \<D>
	have \<D>': "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b 
	  (sb@[Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W]) \<noteq>  {})"
	  by (auto simp: outstanding_refs_append)

	have "(ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> 
	   (ts[i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b,(),\<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,
                     release ?take_sb (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>s\<^sub>b)], 
                m(a:=f \<theta>\<^sub>s\<^sub>b),\<S>)"
	  apply (rule sim_config.intros) 
	  apply    (simp add: m flush_commute ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' sb' \<theta>\<^sub>s\<^sub>b' \<D>\<^sub>s\<^sub>b' )
	  using  share_all_until_volatile_write_Write_commute 
	          [OF i_bound ts\<^sub>s\<^sub>b_i [simplified is\<^sub>s\<^sub>b]]
	  apply   (clarsimp simp add: \<S> \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
	  using  leq
	  apply  (simp add: ts\<^sub>s\<^sub>b')
	  using i_bound i_bound' ts_sim ts_i True \<D>'
	  apply (clarsimp simp add: Let_def nth_list_update 
	    outstanding_refs_conv ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb' \<D>\<^sub>s\<^sub>b' suspend_nothing' flush_all 
	    acquired_append release_append split: if_split_asm)
	  done	

	ultimately 
	show ?thesis
	  using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' valid_sops'
	    valid_dd' load_tmps_fresh' enough_flushs' 
	    valid_program_history' valid' m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' 
	  by (auto simp del: fun_upd_apply)
      next

	case False

	then obtain r where r_in: "r \<in> set sb" and volatile_r: "is_volatile_Write\<^sub>s\<^sub>b r"
	  by (auto simp add: outstanding_refs_conv)
	from takeWhile_dropWhile_real_prefix 
	[OF r_in, of  "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)", simplified, OF volatile_r] 
	obtain a' v' sb'' sop' A' L' R' W' where
	  sb_split: "sb = takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb @ Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# sb''" 
	  and
	  drop: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# sb''"
	  apply (auto)
    subgoal for y ys
	  apply (case_tac y)
	  apply auto
	  done
	  done 
	from drop suspends have suspends: "suspends = Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# sb''"
	  by simp

	have "(ts, m, \<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts, m, \<S>)" by auto

	moreover

	note flush_commute =
	  flush_all_until_volatile_write_append_unflushed [OF False i_bound ts\<^sub>s\<^sub>b_i]

	have "Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W' \<in> set sb"
	  by (subst sb_split) auto
	note drop_app = dropWhile_append1 [OF this, of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)", simplified]

	from \<D>
	have \<D>': "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W]) \<noteq>  {})"
	  by (auto simp: outstanding_refs_append)


	have "(ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> (ts,m,\<S>)"
	  apply (rule sim_config.intros) 
	  apply    (simp add: m flush_commute ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb')
	  using   share_all_until_volatile_write_Write_commute 
	           [OF i_bound ts\<^sub>s\<^sub>b_i [simplified is\<^sub>s\<^sub>b]]
	  apply   (clarsimp simp add: \<S> \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
	  using  leq
	  apply  (simp add: ts\<^sub>s\<^sub>b')
	  using i_bound i_bound' ts_sim ts_i is_sim \<D>'
	  apply (clarsimp simp add: Let_def nth_list_update is_sim drop_app
	    read_tmps_append suspends 
	    prog_instrs_append_Write\<^sub>s\<^sub>b instrs_append_Write\<^sub>s\<^sub>b hd_prog_append_Write\<^sub>s\<^sub>b
	    drop "is\<^sub>s\<^sub>b" ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' 
            \<theta>\<^sub>s\<^sub>b' \<D>\<^sub>s\<^sub>b' acquired_append takeWhile_append1 [OF r_in]
	    volatile_r
	    split: if_split_asm)
	  done
	ultimately show ?thesis
	  using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' valid_dd'
	    valid_sops' load_tmps_fresh' enough_flushs' 
	    valid_program_history' valid' m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' 
	  by (auto simp del: fun_upd_apply )
      qed
    next	
      case (SBHWriteVolatile a D f A L R W)
      then obtain 
	"is\<^sub>s\<^sub>b": "is\<^sub>s\<^sub>b = Write True a (D, f) A L R W# is\<^sub>s\<^sub>b'" and
	\<O>\<^sub>s\<^sub>b': "\<O>\<^sub>s\<^sub>b'=\<O>\<^sub>s\<^sub>b" and
        \<R>\<^sub>s\<^sub>b': "\<R>\<^sub>s\<^sub>b'=\<R>\<^sub>s\<^sub>b" and
	\<theta>\<^sub>s\<^sub>b': "\<theta>\<^sub>s\<^sub>b' = \<theta>\<^sub>s\<^sub>b" and
	\<D>\<^sub>s\<^sub>b': "\<D>\<^sub>s\<^sub>b'=True" and
	sb': "sb'=sb@[Write\<^sub>s\<^sub>b True a (D, f) (f \<theta>\<^sub>s\<^sub>b) A L R W]" and
	m\<^sub>s\<^sub>b': "m\<^sub>s\<^sub>b' = m\<^sub>s\<^sub>b" and
	\<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'=\<S>\<^sub>s\<^sub>b" 
	by auto

      from data_dependency_consistent_instrs [OF i_bound ts\<^sub>s\<^sub>b_i]
      have D_subset: "D \<subseteq> dom \<theta>\<^sub>s\<^sub>b" 
	by (simp add: is\<^sub>s\<^sub>b)

      from safe_memop_flush_sb [simplified is\<^sub>s\<^sub>b] obtain      
	a_unowned_others_ts:
          "\<forall>j<length (map owned ts). i \<noteq> j \<longrightarrow> (a \<notin> owned (ts!j) \<union> dom (released (ts!j)))" and
        L_subset: "L \<subseteq> A" and
	A_shared_owned: "A \<subseteq> dom (share ?drop_sb \<S>) \<union> acquired True sb \<O>\<^sub>s\<^sub>b" and
	R_acq: "R \<subseteq> acquired True sb \<O>\<^sub>s\<^sub>b" and
	A_R: "A \<inter> R = {}" and
        A_unowned_by_others_ts:  
	"\<forall>j<length (map owned ts). i\<noteq>j \<longrightarrow> (A \<inter> (owned (ts!j) \<union> dom (released (ts!j))) = {})" and
	a_not_ro': "a \<notin> read_only (share ?drop_sb \<S>)"
	by cases auto


      from a_unowned_others_ts ts_sim leq
      have a_unowned_others:
        "\<forall>j<length ts\<^sub>s\<^sub>b. i \<noteq> j \<longrightarrow> 
          (let (_,_,_,sb\<^sub>j,_,\<O>\<^sub>j,_) = ts\<^sub>s\<^sub>b!j in 
	    a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j \<and>
            a \<notin> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))" 
  apply (clarsimp simp add: Let_def)
  subgoal for j
	apply (drule_tac x=j in spec)
	apply (auto simp add: dom_release_takeWhile)
	done
  done
(*
      from a_unowned_others_ts ts_sim leq
      have a_unowned_others:
        "\<forall>j<length (map owns_sb ts\<^sub>s\<^sub>b). i \<noteq> j \<longrightarrow> 
          (let (\<O>\<^sub>j,sb\<^sub>j) = (map owns_sb ts\<^sub>s\<^sub>b)!j in 
	    a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j \<and>
            a \<notin> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))" 
	apply (clarsimp simp add: Let_def)
	apply (drule_tac x=j in spec)
	apply (auto simp add: dom_release_takeWhile)
	done
*)
(*
      from a_unowned_others
      have a_unacquired_others:
        "\<forall>j<length ts\<^sub>s\<^sub>b. i \<noteq> j \<longrightarrow> 
          (let (_,_,_,sb\<^sub>j,_,_) = ts\<^sub>s\<^sub>b!j in 
	    a \<notin> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))" 
	by (auto simp add: acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)
*)
      have a_not_ro: "a \<notin> read_only (share sb \<S>\<^sub>s\<^sub>b)"
      proof 
	assume a: "a \<in> read_only (share sb \<S>\<^sub>s\<^sub>b)"
	from local.read_only_unowned_axioms have "read_only_unowned \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b".
        from in_read_only_share_all_until_volatile_write' [OF ownership_distinct_ts\<^sub>s\<^sub>b sharing_consis_ts\<^sub>s\<^sub>b
          \<open>read_only_unowned \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> i_bound ts\<^sub>s\<^sub>b_i a_unowned_others a] 
	have "a \<in> read_only (share ?drop_sb \<S>)"
	  by (simp add: \<S>)
	with a_not_ro' show False by simp
      qed
      
      from A_unowned_by_others_ts ts_sim leq
      have A_unowned_by_others:  
	"\<forall>j<length ts\<^sub>s\<^sub>b. i\<noteq>j \<longrightarrow> (let (_,_,_,sb\<^sub>j,_,\<O>\<^sub>j,_) = ts\<^sub>s\<^sub>b!j 
	  in A \<inter> (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j \<union>
                  all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)) = {})" 
  apply (clarsimp simp add: Let_def)
  subgoal for j
	apply (drule_tac x=j in spec)
	apply (force simp add: dom_release_takeWhile)
	done
  done
      have a_not_acquired_others: "\<forall>j<length (map \<O>_sb ts\<^sub>s\<^sub>b). i \<noteq> j \<longrightarrow> 
        (let (\<O>\<^sub>j,sb\<^sub>j) = (map \<O>_sb ts\<^sub>s\<^sub>b)!j in a \<notin> all_acquired sb\<^sub>j)" 
      proof -
	{
	  fix j \<O>\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length (map owned ts\<^sub>s\<^sub>b)"
	  assume neq_i_j: "i\<noteq>j"
	  assume ts\<^sub>s\<^sub>b_j: "(map \<O>_sb ts\<^sub>s\<^sub>b)!j = (\<O>\<^sub>j,sb\<^sub>j)"
	  assume conflict: "a \<in> all_acquired sb\<^sub>j"
	  have False
	  proof -
	    from j_bound leq
	    have j_bound': "j < length (map owned ts)"
	      by auto
	    from j_bound have j_bound'': "j < length ts\<^sub>s\<^sub>b"
	      by auto
	    from j_bound' have j_bound''': "j < length ts"
	      by simp

	    let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"

	    from ts_sim [rule_format, OF  j_bound''] ts\<^sub>s\<^sub>b_j j_bound''
            
	    obtain p\<^sub>j suspends\<^sub>j "is\<^sub>s\<^sub>b\<^sub>j" \<R>\<^sub>j \<D>\<^sub>s\<^sub>b\<^sub>j \<D>\<^sub>j \<theta>\<^sub>s\<^sub>b\<^sub>j "is\<^sub>j" where
		  ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j, \<theta>\<^sub>s\<^sub>b\<^sub>j, sb\<^sub>j, \<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"  and
		  suspends\<^sub>j: "suspends\<^sub>j = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j" and
		  is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
	          \<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
		  ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
                               \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), 
	                       \<D>\<^sub>j, 
                               acquired True ?take_sb\<^sub>j \<O>\<^sub>j,
                               release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	      apply (cases "ts\<^sub>s\<^sub>b!j")
	      apply (force simp add: Let_def)
	      done

            
	    from a_unowned_others [rule_format,OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
	    obtain a_unacq: "a \<notin> acquired True ?take_sb\<^sub>j \<O>\<^sub>j" and a_not_shared: "a \<notin> all_shared ?take_sb\<^sub>j"
	      by auto
            have conflict_drop: "a \<in> all_acquired suspends\<^sub>j"
            proof (rule ccontr)
              assume "a \<notin> all_acquired suspends\<^sub>j"
              with all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j] conflict
              have "a \<in> all_acquired ?take_sb\<^sub>j"
                by (auto simp add: suspends\<^sub>j)
              from all_acquired_unshared_acquired [OF this a_not_shared] a_unacq
              show False by auto
            qed


	    from j_bound''' i_bound' have j_bound_ts': "j < length ?ts'"
	      by simp

	    (* FIXME: extract common intermediate steps of both cases*)
	    from split_all_acquired_in [OF conflict_drop]
	    show ?thesis
	    proof
	      assume "\<exists>sop a' v ys zs A L R W. 
                suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W# zs \<and> a \<in> A"
	      then 
	      obtain a' sop' v' ys zs A' L' R' W' where
		split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# zs" 
		(is "suspends\<^sub>j = ?suspends") and
		a_A': "a \<in> A'"
		by blast

	      from sharing_consis [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have sharing_consis_j: "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	      then have A'_R': "A' \<inter> R' = {}" 
		by (simp add: sharing_consistent_append [of _ _ ?take_sb\<^sub>j ?drop_sb\<^sub>j, simplified] 
		  suspends\<^sub>j [symmetric] split_suspends\<^sub>j sharing_consistent_append)
	      from valid_program_history [OF j_bound'' ts\<^sub>s\<^sub>b_j] 
	      have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	      then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
		apply -
		apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply (simp add: split_suspends\<^sub>j)
		done

	      from ts\<^sub>j neq_i_j j_bound 
	      have ts'_j: "?ts'!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
		\<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), 
		\<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
		by auto
	      from valid_last_prog [OF j_bound'' ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	      then
	      have lp: "last_prog p\<^sub>j suspends\<^sub>j = p\<^sub>j"
		apply -
		apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply simp
		done


	      from valid_reads [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have reads_consis_j: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".

	      from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> 
		j_bound'' ts\<^sub>s\<^sub>b_j this]
	      have reads_consis_m_j: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
		by (simp add: m suspends\<^sub>j)

	      from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound'' neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j]
	      have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
		by (simp add: suspends\<^sub>j)
	      from reads_consistent_flush_independent [OF this reads_consis_m_j]
	      have reads_consis_flush_suspend: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
		(flush ?drop_sb m) suspends\<^sub>j".

	      hence reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)  
		(flush ?drop_sb m) (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'])"
		by (simp add: split_suspends\<^sub>j reads_consistent_append)

	      from valid_write_sops [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		valid_sops_drop: "\<forall>sop\<in>write_sops (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']). valid_sop sop"
		apply (simp only: write_sops_append)
		apply auto
		done

	      from read_tmps_distinct [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      then obtain 
		read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
		distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		apply (simp only: distinct_read_tmps_append)
		done

	      from valid_history [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have h_consis: 
		"history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply simp
		done
	    
	      have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	      proof -
		from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		  by simp
		from last_prog_hd_prog_append' [OF h_consis] this
		have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		  by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		moreover 
		have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		  last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		  apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		  by (rule last_prog_hd_prog_append)
		ultimately show ?thesis
		  by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      qed

	      from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
		h_consis] last_prog_hd_prog
	      have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      from reads_consistent_drop_volatile_writes_no_volatile_reads  
	      [OF reads_consis_j] 
	      have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b 
		(ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) = {}"
		by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		  split_suspends\<^sub>j )

	      have acq_simp:
		"acquired True (ys @ [Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) 
                    (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) = 
                 acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R'"
		by (simp add: acquired_append)

	      from flush_store_buffer_append [where sb="ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']" and sb'="zs", simplified,
	      OF j_bound_ts' is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
	      ts'_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_ys 
	      hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
	      distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
		no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
	      \<S>="share ?drop_sb \<S>"]
	      obtain is\<^sub>j' \<R>\<^sub>j' where
		is\<^sub>j': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs" and
		steps_ys: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>)  \<Rightarrow>\<^sub>d\<^sup>* 
		  (?ts'[j:=(last_prog
                              (hd_prog p\<^sub>j (Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# zs)) (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']),
                             is\<^sub>j',
                             \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps zs),
                              (), True, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R',\<R>\<^sub>j')],
                    flush (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) (flush ?drop_sb m),
                    share (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) (share ?drop_sb \<S>))"
		   (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
                by (auto simp add: acquired_append outstanding_refs_append)

	      from i_bound' have i_bound_ys: "i < length ?ts_ys"
		by auto

	      from i_bound' neq_i_j 
	      have ts_ys_i: "?ts_ys!i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b,(), 
		\<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b, release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
		by simp
	      note conflict_computation = rtranclp_trans [OF steps_flush_sb steps_ys]
	      
	      from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	      have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	      
	      from safe_delayedE [OF this i_bound_ys ts_ys_i, simplified is\<^sub>s\<^sub>b] 
	      have a_unowned: 
		"\<forall>j < length ?ts_ys. i\<noteq>j \<longrightarrow> (let (\<O>\<^sub>j) = map owned ?ts_ys!j in a \<notin> \<O>\<^sub>j)"
		apply cases
		apply (auto simp add: Let_def is\<^sub>s\<^sub>b)
		done
	      from a_A' a_unowned [rule_format, of j] neq_i_j j_bound' A'_R'
	      show False
		by (auto simp add: Let_def)
	    next
	      assume "\<exists>A L R W ys zs. suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A"
	      then 
	      obtain A' L' R' W' ys zs where
		split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs" 
		(is "suspends\<^sub>j = ?suspends") and
		  a_A': "a \<in> A'"
		by blast

	      from sharing_consis [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have sharing_consis_j: "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	      then have A'_R': "A' \<inter> R' = {}" 
		by (simp add: sharing_consistent_append [of _ _ ?take_sb\<^sub>j ?drop_sb\<^sub>j, simplified] 
		  suspends\<^sub>j [symmetric] split_suspends\<^sub>j sharing_consistent_append)
	      from valid_program_history [OF j_bound'' ts\<^sub>s\<^sub>b_j] 
	      have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	      then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
		apply -
		apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply (simp add: split_suspends\<^sub>j)
		done

	      from ts\<^sub>j neq_i_j j_bound 
	      have ts'_j: "?ts'!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
		\<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), 
		\<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j, release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
		by auto
	      from valid_last_prog [OF j_bound'' ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	      then
	      have lp: "last_prog p\<^sub>j suspends\<^sub>j = p\<^sub>j"
		apply -
		apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply simp
		done


	      from valid_reads [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have reads_consis_j: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	      from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> 
		j_bound'' ts\<^sub>s\<^sub>b_j this]
	      have reads_consis_m_j: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
		by (simp add: m suspends\<^sub>j)

	      from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound'' neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j]
	      have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
		by (simp add: suspends\<^sub>j)
	      from reads_consistent_flush_independent [OF this reads_consis_m_j]
	      have reads_consis_flush_suspend: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
		(flush ?drop_sb m) suspends\<^sub>j".

	      hence reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)  
		(flush ?drop_sb m) (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W'])"
		by (simp add: split_suspends\<^sub>j reads_consistent_append)

	      from valid_write_sops [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		valid_sops_drop: "\<forall>sop\<in>write_sops (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']). valid_sop sop"
		apply (simp only: write_sops_append)
		apply auto
		done

	      from read_tmps_distinct [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      then obtain 
		read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
		distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		apply (simp only: distinct_read_tmps_append)
		done

	      from valid_history [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have h_consis: 
		"history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply simp
		done
	    
	      have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	      proof -
		from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		  by simp
		from last_prog_hd_prog_append' [OF h_consis] this
		have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		  by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		moreover 
		have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		  last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		  apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		  by (rule last_prog_hd_prog_append)
		ultimately show ?thesis
		  by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      qed

	      from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
		h_consis] last_prog_hd_prog
	      have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      from reads_consistent_drop_volatile_writes_no_volatile_reads  
	      [OF reads_consis_j] 
	      have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b 
		(ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) = {}"
		by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		  split_suspends\<^sub>j )

	      have acq_simp:
		"acquired True (ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W']) 
                    (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) = 
                 acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R'"
		by (simp add: acquired_append)

	      from flush_store_buffer_append [where sb="ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']" and sb'="zs", simplified,
	      OF j_bound_ts' is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
	      ts'_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_ys 
	      hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
	      distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
	      no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
	      \<S>="share ?drop_sb \<S>"]
	      obtain is\<^sub>j' \<R>\<^sub>j'  where
		is\<^sub>j': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs" and
		steps_ys: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>)  \<Rightarrow>\<^sub>d\<^sup>* 
		  (?ts'[j:=(last_prog
                              (hd_prog p\<^sub>j (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)) (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']),
                             is\<^sub>j',
                             \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps zs),
                              (),
                             \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W']) \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R',\<R>\<^sub>j')],
                    flush (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) (flush ?drop_sb m),
                    share (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) (share ?drop_sb \<S>))"
		   (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
                by (auto simp add: acquired_append)

	      from i_bound' have i_bound_ys: "i < length ?ts_ys"
		by auto

	      from i_bound' neq_i_j 
	      have ts_ys_i: "?ts_ys!i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b,\<theta>\<^sub>s\<^sub>b,(), 
		\<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b, release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
		by simp
	      note conflict_computation = rtranclp_trans [OF steps_flush_sb steps_ys]
	      
	      from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	      have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	      
	      from safe_delayedE [OF this i_bound_ys ts_ys_i, simplified is\<^sub>s\<^sub>b] 
	      have a_unowned: 
		"\<forall>j < length ?ts_ys. i\<noteq>j \<longrightarrow> (let (\<O>\<^sub>j) = map owned ?ts_ys!j in a \<notin> \<O>\<^sub>j)"
		apply cases
		apply (auto simp add: Let_def is\<^sub>s\<^sub>b)
		done
	      from a_A' a_unowned [rule_format, of j] neq_i_j j_bound' A'_R'
	      show False
		by (auto simp add: Let_def)
	    qed
	  qed
	}
	thus ?thesis
	  by (auto simp add: Let_def)
      qed

       
      have A_unused_by_others:
	  "\<forall>j<length (map \<O>_sb ts\<^sub>s\<^sub>b). i \<noteq> j \<longrightarrow>
             (let (\<O>\<^sub>j, sb\<^sub>j) = map \<O>_sb ts\<^sub>s\<^sub>b! j
             in A \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j = {})"
      proof -
	{
	  fix j \<O>\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length (map owned ts\<^sub>s\<^sub>b)"
	  assume neq_i_j: "i\<noteq>j"
	  assume ts\<^sub>s\<^sub>b_j: "(map \<O>_sb ts\<^sub>s\<^sub>b)!j = (\<O>\<^sub>j,sb\<^sub>j)"
	  assume conflict: "A \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {}"
	  have False
	  proof -
	    from j_bound leq
	    have j_bound': "j < length (map owned ts)"
	      by auto
	    from j_bound have j_bound'': "j < length ts\<^sub>s\<^sub>b"
	      by auto
	    from j_bound' have j_bound''': "j < length ts"
	      by simp
	    
	    from conflict obtain a' where
	      a'_in: "a' \<in> A" and
              a'_in_j: "a' \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
	      by auto

	    let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"

	    from ts_sim [rule_format, OF  j_bound''] ts\<^sub>s\<^sub>b_j j_bound''
	    obtain p\<^sub>j suspends\<^sub>j "is\<^sub>s\<^sub>b\<^sub>j" \<D>\<^sub>s\<^sub>b\<^sub>j \<D>\<^sub>j \<R>\<^sub>j \<theta>\<^sub>s\<^sub>b\<^sub>j "is\<^sub>j" where
	      ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j, \<theta>\<^sub>s\<^sub>b\<^sub>j, sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
	      suspends\<^sub>j: "suspends\<^sub>j = ?drop_sb\<^sub>j" and
	      is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
	      \<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
	      ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
	             \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), \<D>\<^sub>j, 
                     acquired True ?take_sb\<^sub>j \<O>\<^sub>j,
                     release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	      apply (cases "ts\<^sub>s\<^sub>b!j")
	      apply (force simp add: Let_def)
	      done
	      
	    have "a' \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b suspends\<^sub>j"
	    proof -	
	      from a'_in_j 
	      have "a' \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (?take_sb\<^sub>j @ ?drop_sb\<^sub>j)"
		by simp
	      thus ?thesis
		apply (simp only: outstanding_refs_append suspends\<^sub>j)
		apply (auto simp add: outstanding_refs_conv dest: set_takeWhileD)
		done
	    qed
		
	    from split_volatile_Write\<^sub>s\<^sub>b_in_outstanding_refs [OF this]
	    obtain sop v ys zs A' L' R' W' where
	      split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a' sop v A' L' R' W'# zs" (is "suspends\<^sub>j = ?suspends")
	      by blast
	    
	    from direct_memop_step.WriteVolatile [where  \<theta>=\<theta>\<^sub>s\<^sub>b and m="flush ?drop_sb m"]
	    have "(Write True a (D, f) A L R W# is\<^sub>s\<^sub>b', 
                       \<theta>\<^sub>s\<^sub>b, (), flush ?drop_sb m,\<D>\<^sub>s\<^sub>b,acquired True sb \<O>\<^sub>s\<^sub>b,
                        release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b, 
                        share ?drop_sb \<S>) \<rightarrow> 
                    (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), (flush ?drop_sb m)(a := f \<theta>\<^sub>s\<^sub>b), True, acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R, Map.empty,
                      share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

	    from direct_computation.concurrent_step.Memop [OF 
	      i_bound_ts' [simplified is\<^sub>s\<^sub>b] ts'_i [simplified is\<^sub>s\<^sub>b] this [simplified is\<^sub>s\<^sub>b]] 
	    have store_step: "(?ts', flush ?drop_sb m,share ?drop_sb \<S> ) \<Rightarrow>\<^sub>d 
                    (?ts'[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), 
                         True, acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)], 
                         (flush ?drop_sb m)(a := f \<theta>\<^sub>s\<^sub>b), share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L )"
		  (is " _ \<Rightarrow>\<^sub>d (?ts_A, ?m_A, ?share_A)")
	     by (simp add: is\<^sub>s\<^sub>b)
	      
	       
	   from i_bound' have i_bound'': "i < length ?ts_A"
	     by simp

	   from valid_program_history [OF j_bound'' ts\<^sub>s\<^sub>b_j] 
	   have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	   then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
	     apply -
	     apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
	     apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	     apply (simp add: split_suspends\<^sub>j)
	     done
	   
	   from ts\<^sub>j neq_i_j j_bound 
	   have ts_A_j: "?ts_A!j = (hd_prog p\<^sub>j (ys @ Write\<^sub>s\<^sub>b True a' sop v A' L' R' W'# zs), is\<^sub>j,
	     \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (ys @ Write\<^sub>s\<^sub>b True a' sop v A' L' R' W'# zs)), (), \<D>\<^sub>j, 
	     acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	     by (simp add: split_suspends\<^sub>j)


	   from j_bound''' i_bound' neq_i_j have j_bound'''': "j < length ?ts_A"
	     by simp

	   from valid_last_prog [OF j_bound'' ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	   then
	   have lp: "last_prog p\<^sub>j ?suspends = p\<^sub>j"
	     apply -
	     apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
	     apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	     apply simp
	     done

	   from valid_reads [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have reads_consis: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".

	   from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> j_bound''
	     ts\<^sub>s\<^sub>b_j reads_consis]
	   have reads_consis_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
	     by (simp add: m suspends\<^sub>j)

	   from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound'' neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j]
	   have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
	     by (simp add: suspends\<^sub>j)
	   from reads_consistent_flush_independent [OF this reads_consis_m]
	   have reads_consis_flush_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
	     (flush ?drop_sb m) suspends\<^sub>j".

	   from a_unowned_others [rule_format, OF _ neq_i_j] j_bound ts\<^sub>s\<^sub>b_j
	   obtain a_notin_owns_j: "a \<notin> acquired True ?take_sb\<^sub>j \<O>\<^sub>j" and a_unshared: "a \<notin> all_shared ?take_sb\<^sub>j"
	     by auto
	   from a_not_acquired_others [rule_format, OF _ neq_i_j] j_bound ts\<^sub>s\<^sub>b_j
	   have a_not_acquired_j: "a \<notin> all_acquired sb\<^sub>j"
	     by auto
	   
	   from outstanding_non_volatile_refs_owned_or_read_only [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have nvo_j: "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	   
	   (* FIXME: make this a lemma, duplicated some times below *)
	   have a_no_non_vol_read: "a \<notin> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?drop_sb\<^sub>j"
	   proof 
	     assume a_in_nvr:"a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?drop_sb\<^sub>j"

	     from reads_consistent_drop [OF reads_consis]
	     have rc: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) (flush ?take_sb\<^sub>j m\<^sub>s\<^sub>b) ?drop_sb\<^sub>j".

	     from non_volatile_owned_or_read_only_drop [OF nvo_j]
	     have nvo_j_drop: "non_volatile_owned_or_read_only True (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)
	       (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)
	       ?drop_sb\<^sub>j"
	       by simp

	     from outstanding_refs_non_volatile_Read\<^sub>s\<^sub>b_all_acquired [OF rc this a_in_nvr]

	     have a_owns_acq_ror: 
	       "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j \<union> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
	       by (auto dest!: acquired_all_acquired_in all_acquired_takeWhile_dropWhile_in
		 simp add: acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)

	     have a_unowned_j: "a \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
             proof (cases "a \<in> \<O>\<^sub>j")
               case False with a_not_acquired_j show ?thesis by auto
             next
               case True
               from all_shared_acquired_in [OF True a_unshared] a_notin_owns_j
               have False by auto thus ?thesis ..
             qed
	     with a_owns_acq_ror 
	     have a_ror: "a \<in> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
	       by auto

	     with read_only_reads_unowned [OF j_bound'' i_bound neq_i_j [symmetric] ts\<^sub>s\<^sub>b_j ts\<^sub>s\<^sub>b_i]
	     have a_unowned_sb: "a \<notin> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
	       by auto
	       
	     from sharing_consis [OF j_bound'' ts\<^sub>s\<^sub>b_j] sharing_consistent_append [of \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	     have consis_j_drop: "sharing_consistent (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b) (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
	       by auto
             
	     from read_only_reads_read_only [OF nvo_j_drop consis_j_drop] a_ror a_unowned_j
	       all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j] acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b [of sb\<^sub>j \<O>\<^sub>j]
	     have "a \<in> read_only (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
	       by (auto simp add: )
             from read_only_share_all_shared [OF this] a_unshared
	     have "a \<in> read_only \<S>\<^sub>s\<^sub>b"
	       by fastforce
	      
	     from read_only_unacquired_share [OF read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] 
	       weak_sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i] this] a_unowned_sb
	     have "a \<in> read_only (share sb \<S>\<^sub>s\<^sub>b)"
	       by auto
	   
	     with a_not_ro show False
	       by simp
	   qed
	 
	   with reads_consistent_mem_eq_on_non_volatile_reads  [OF _ subset_refl reads_consis_flush_m]
	   have "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?m_A suspends\<^sub>j"
	     by (auto simp add: suspends\<^sub>j)


	   hence reads_consis_m_A_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?m_A ys"
	     by (simp add: split_suspends\<^sub>j reads_consistent_append)

	   from valid_history [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have h_consis: 
	     "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
	     apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	     apply simp
	     done

	   have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	   proof -
	     from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
	       by simp
	     from last_prog_hd_prog_append' [OF h_consis] this
	     have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
	       by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	     moreover 
	     have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		  last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
	       apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	       by (rule last_prog_hd_prog_append)
	     ultimately show ?thesis
	       by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	   qed

	   from valid_write_sops [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
	     by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	   then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
	     valid_sops_drop: "\<forall>sop\<in>write_sops ys. valid_sop sop"
	     apply (simp only: write_sops_append )
	     apply auto
	     done

	   from read_tmps_distinct [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
	     by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	   then obtain 
	     read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
	     distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
	     apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	     apply (simp only: distinct_read_tmps_append)
	     done
	   
	   from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop h_consis]	  
	     last_prog_hd_prog
	   have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
	     by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	    from reads_consistent_drop_volatile_writes_no_volatile_reads  
	    [OF reads_consis] 
	    have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b ys = {}"
	      by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		split_suspends\<^sub>j )
	   
	    from flush_store_buffer_append [
	      OF j_bound''''  is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
	      ts_A_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_m_A_ys
	      hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
	      no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
	      \<S>="?share_A"]
	    obtain is\<^sub>j' \<R>\<^sub>j' where
	      is\<^sub>j': "instrs (Write\<^sub>s\<^sub>b True a' sop v A' L' R' W'# zs) @ is\<^sub>s\<^sub>b\<^sub>j = 
	            is\<^sub>j' @ prog_instrs (Write\<^sub>s\<^sub>b True a' sop v A' L' R' W'# zs)" and
	      steps_ys: "(?ts_A, ?m_A, ?share_A)  \<Rightarrow>\<^sub>d\<^sup>* 
		(?ts_A[j:= (last_prog (hd_prog p\<^sub>j (Write\<^sub>s\<^sub>b True a' sop v A' L' R' W'# zs)) ys,
                           is\<^sub>j',
                           \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Write\<^sub>s\<^sub>b True a' sop v A' L' R' W' # zs)),(),
                           \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j') ],
                  flush ys ?m_A,
                  share ys ?share_A)"
		 (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
              by (auto)

	    note conflict_computation = rtranclp_trans [OF rtranclp_r_rtranclp [OF steps_flush_sb, OF store_step] steps_ys]
	    from cph
	    have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ((ys @ [Write\<^sub>s\<^sub>b True a' sop v A' L' R' W']) @ zs)"
	      by simp
	    from causal_program_history_suffix [OF this]
	    have cph': "causal_program_history is\<^sub>s\<^sub>b\<^sub>j zs".	      
	    interpret causal\<^sub>j: causal_program_history "is\<^sub>s\<^sub>b\<^sub>j" "zs" by (rule cph')

	    from causal\<^sub>j.causal_program_history [of "[]", simplified, OF refl] is\<^sub>j'   
	    obtain is\<^sub>j''
	      where is\<^sub>j': "is\<^sub>j' = Write True a' sop A' L' R' W'#is\<^sub>j''" and
	      is\<^sub>j'': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j'' @ prog_instrs zs"
	      by clarsimp

	    from j_bound'''
	    have j_bound_ys: "j < length ?ts_ys"
	      by auto

	    from j_bound_ys neq_i_j
	    have ts_ys_j: "?ts_ys!j=(last_prog (hd_prog p\<^sub>j (Write\<^sub>s\<^sub>b True a' sop v A' L' R' W'# zs)) ys, is\<^sub>j',
                 \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Write\<^sub>s\<^sub>b True a' sop v A' L' R' W'# zs)),(),
	         \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {},
                 acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')"
	      by auto

	    from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	    have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	    
	    from safe_delayedE [OF this j_bound_ys ts_ys_j, simplified is\<^sub>j']
	    have a_unowned: 
		"\<forall>i < length ?ts_ys. j\<noteq>i \<longrightarrow> (let (\<O>\<^sub>i) = map owned ?ts_ys!i in a' \<notin> \<O>\<^sub>i)"
	      apply cases
	      apply (auto simp add: Let_def is\<^sub>s\<^sub>b)
	      done
	    from a'_in a_unowned [rule_format, of i] neq_i_j i_bound' A_R
	    show False
	      by (auto simp add: Let_def)
	  qed
	}
	thus ?thesis
	  by (auto simp add: Let_def)
      qed
      
      have A_unaquired_by_others:
	  "\<forall>j<length (map \<O>_sb ts\<^sub>s\<^sub>b). i \<noteq> j \<longrightarrow>
             (let (\<O>\<^sub>j, sb\<^sub>j) = map \<O>_sb ts\<^sub>s\<^sub>b! j
             in A \<inter> all_acquired sb\<^sub>j = {})"
      proof -
	{
	  fix j \<O>\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length (map owned ts\<^sub>s\<^sub>b)"
	  assume neq_i_j: "i\<noteq>j"
	  assume ts\<^sub>s\<^sub>b_j: "(map \<O>_sb ts\<^sub>s\<^sub>b)!j = (\<O>\<^sub>j,sb\<^sub>j)"
	  assume conflict: "A \<inter> all_acquired sb\<^sub>j \<noteq> {}"
	  have False
	  proof -
	    from j_bound leq
	    have j_bound': "j < length (map owned ts)"
	      by auto
	    from j_bound have j_bound'': "j < length ts\<^sub>s\<^sub>b"
	      by auto
	    from j_bound' have j_bound''': "j < length ts"
	      by simp
	    
	    from conflict obtain a' where
	      a'_in: "a' \<in> A" and
              a'_in_j: "a' \<in> all_acquired sb\<^sub>j"
	      by auto

	    let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"

	    from ts_sim [rule_format, OF  j_bound''] ts\<^sub>s\<^sub>b_j j_bound''
	    obtain p\<^sub>j suspends\<^sub>j "is\<^sub>s\<^sub>b\<^sub>j" \<D>\<^sub>s\<^sub>b\<^sub>j \<D>\<^sub>j \<R>\<^sub>j \<theta>\<^sub>s\<^sub>b\<^sub>j "is\<^sub>j" where
	      ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j, \<theta>\<^sub>s\<^sub>b\<^sub>j, sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
	      suspends\<^sub>j: "suspends\<^sub>j = ?drop_sb\<^sub>j" and
	      is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
	      \<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
	      ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j, 
	                   \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), 
	                   \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	      apply (cases "ts\<^sub>s\<^sub>b!j")
	      apply (force simp add: Let_def)
	      done

	    from a'_in_j all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	    have "a' \<in> all_acquired ?take_sb\<^sub>j \<or> a' \<in> all_acquired suspends\<^sub>j"
	      by (auto simp add: suspends\<^sub>j)
	    thus False
	    proof 
	      assume "a' \<in> all_acquired ?take_sb\<^sub>j"
	      with A_unowned_by_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound a'_in
	      show False
		by (auto dest: all_acquired_unshared_acquired)
	    next
	      assume conflict_drop: "a' \<in> all_acquired suspends\<^sub>j"
	      from split_all_acquired_in [OF conflict_drop]
	      (* FIXME: exract common parts *)
	      show False
	      proof 
		assume "\<exists>sop a'' v ys zs A L R W. 
                         suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a'' sop v A L R W# zs \<and> a' \<in> A" 
	        then
		obtain a'' sop' v' ys zs A' L' R' W' where
		  split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W'# zs" 
		    (is "suspends\<^sub>j = ?suspends") and
		  a'_A': "a' \<in> A'"
		 by auto
	    
	       from direct_memop_step.WriteVolatile [where  \<theta>=\<theta>\<^sub>s\<^sub>b and m="flush ?drop_sb m"]
	       have "(Write True a (D, f) A L R W # is\<^sub>s\<^sub>b', 
                         \<theta>\<^sub>s\<^sub>b, (), flush ?drop_sb m ,\<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b,
                         release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b, 
                         share ?drop_sb \<S>) \<rightarrow> 
                    (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), (flush ?drop_sb m)(a := f \<theta>\<^sub>s\<^sub>b), True, acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty, 
                      share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

	       from direct_computation.concurrent_step.Memop [OF 
		 i_bound_ts' [simplified is\<^sub>s\<^sub>b] ts'_i [simplified is\<^sub>s\<^sub>b] this [simplified is\<^sub>s\<^sub>b]] 

	       have store_step: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>) \<Rightarrow>\<^sub>d 
                   (?ts'[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b',
		        \<theta>\<^sub>s\<^sub>b, (),True, acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)], 
                         (flush ?drop_sb m)(a := f \<theta>\<^sub>s\<^sub>b),share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		   (is " _ \<Rightarrow>\<^sub>d (?ts_A, ?m_A, ?share_A)")
		 by (simp add: is\<^sub>s\<^sub>b)
	      
	       
	       from i_bound' have i_bound'': "i < length ?ts_A"
		 by simp

	       from valid_program_history [OF j_bound'' ts\<^sub>s\<^sub>b_j] 
	       have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	       then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
		 apply -
		 apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		 apply (simp add: split_suspends\<^sub>j)
		 done
	       
	       from ts\<^sub>j neq_i_j j_bound 
	       have ts_A_j: "?ts_A!j = (hd_prog p\<^sub>j (ys @ Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W'# zs), is\<^sub>j, 
		   \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (ys @ Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W'# zs)), (), \<D>\<^sub>j, 
		   acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
		 by (simp add: split_suspends\<^sub>j)


	       from j_bound''' i_bound' neq_i_j have j_bound'''': "j < length ?ts_A"
		 by simp

	       from valid_last_prog [OF j_bound'' ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	       then
	       have lp: "last_prog p\<^sub>j ?suspends = p\<^sub>j"
		 apply -
		 apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		 apply simp
		 done
	       
	       from valid_reads [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have reads_consis: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	       
	       from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> 
		 j_bound''
		 ts\<^sub>s\<^sub>b_j reads_consis]
	       have reads_consis_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
		 by (simp add: m suspends\<^sub>j)

	       from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound'' neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j]
	       have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
		 by (simp add: suspends\<^sub>j)
	       from reads_consistent_flush_independent [OF this reads_consis_m]
	       have reads_consis_flush_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
		 (flush ?drop_sb m) suspends\<^sub>j".
       
	       from a_unowned_others [rule_format, OF _ neq_i_j] j_bound ts\<^sub>s\<^sub>b_j
	       obtain a_notin_owns_j: "a \<notin> acquired True ?take_sb\<^sub>j \<O>\<^sub>j" and a_unshared: "a \<notin> all_shared ?take_sb\<^sub>j"
	         by auto
	       from a_not_acquired_others [rule_format, OF _ neq_i_j] j_bound ts\<^sub>s\<^sub>b_j
	       have a_not_acquired_j: "a \<notin> all_acquired sb\<^sub>j"
		 by auto
	       
	       from outstanding_non_volatile_refs_owned_or_read_only [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have nvo_j: "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".

	       have a_no_non_vol_read: "a \<notin> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?drop_sb\<^sub>j"
	       proof 
		 assume a_in_nvr:"a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?drop_sb\<^sub>j"
		 
		 from reads_consistent_drop [OF reads_consis]
		 have rc: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) (flush ?take_sb\<^sub>j m\<^sub>s\<^sub>b) ?drop_sb\<^sub>j".
		 
		 from non_volatile_owned_or_read_only_drop [OF nvo_j]
		 have nvo_j_drop: "non_volatile_owned_or_read_only True (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)
		   (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)
		   ?drop_sb\<^sub>j"
		   by simp
		 
		 from outstanding_refs_non_volatile_Read\<^sub>s\<^sub>b_all_acquired [OF rc this a_in_nvr]

		 have a_owns_acq_ror: 
		   "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j \<union> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
		   by (auto dest!: acquired_all_acquired_in all_acquired_takeWhile_dropWhile_in
		     simp add: acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)
		 have a_unowned_j: "a \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
                 proof (cases "a \<in> \<O>\<^sub>j")
                   case False with a_not_acquired_j show ?thesis by auto
                 next
                   case True
                   from all_shared_acquired_in [OF True a_unshared] a_notin_owns_j
                   have False by auto thus ?thesis ..
                 qed

		 
		 with a_owns_acq_ror 
		 have a_ror: "a \<in> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
		   by auto
		 
		 with read_only_reads_unowned [OF j_bound'' i_bound neq_i_j [symmetric] ts\<^sub>s\<^sub>b_j ts\<^sub>s\<^sub>b_i]
		 have a_unowned_sb: "a \<notin> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
		   by auto
		 
		 from sharing_consis [OF j_bound'' ts\<^sub>s\<^sub>b_j] sharing_consistent_append [of \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		 have consis_j_drop: "sharing_consistent (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b) (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
		   by auto
		 
		 from read_only_reads_read_only [OF nvo_j_drop consis_j_drop] a_ror a_unowned_j
		   all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j] acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b [of sb\<^sub>j \<O>\<^sub>j]
		 have "a \<in> read_only (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
		   by (auto)
		 from read_only_share_all_shared [OF this] a_unshared
		 have "a \<in> read_only \<S>\<^sub>s\<^sub>b"
		   by fastforce
	      
		 from read_only_unacquired_share [OF read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] 
		   weak_sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i] this] a_unowned_sb
		 have "a \<in> read_only (share sb \<S>\<^sub>s\<^sub>b)"
		   by auto
		 
		 with a_not_ro show False
		   by simp
	       qed
	       with reads_consistent_mem_eq_on_non_volatile_reads  [OF _ subset_refl reads_consis_flush_m]
	       have "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?m_A suspends\<^sub>j"
		 by (auto simp add: suspends\<^sub>j)
	       
	       hence reads_consis_m_A_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?m_A ys"
		 by (simp add: split_suspends\<^sub>j reads_consistent_append)

	       
	       from valid_history [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have h_consis: 
		 "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		 apply simp
		 done
	       
	       have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	       proof -
		 from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		   by simp
		 from last_prog_hd_prog_append' [OF h_consis] this
		 have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		   by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		 moreover 
		 have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		   last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		   apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		   by (rule last_prog_hd_prog_append)
		 ultimately show ?thesis
		   by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	       qed
	       
	       from valid_write_sops [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
		 by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	       then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		 valid_sops_drop: "\<forall>sop\<in>write_sops ys. valid_sop sop"
		 apply (simp only: write_sops_append )
		 apply auto
		 done
	       
	       from read_tmps_distinct [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
		 by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	       then obtain 
		 read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
		 distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		 apply (simp only: distinct_read_tmps_append)
		 done
	       
	       from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop h_consis]	  
		 last_prog_hd_prog
	       have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
		 by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	       from reads_consistent_drop_volatile_writes_no_volatile_reads  
	       [OF reads_consis] 
	       have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b ys = {}"
		 by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		   split_suspends\<^sub>j )
	       
	       from flush_store_buffer_append [
		 OF j_bound''''  is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
		 ts_A_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_m_A_ys
		 hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
		 no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
		 \<S>="?share_A"]
	       obtain is\<^sub>j' \<R>\<^sub>j' where
		 is\<^sub>j': "instrs (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs) @ is\<^sub>s\<^sub>b\<^sub>j = 
	            is\<^sub>j' @ prog_instrs (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs)" and
		 steps_ys: "(?ts_A, ?m_A, ?share_A)  \<Rightarrow>\<^sub>d\<^sup>* 
		(?ts_A[j:= (last_prog (hd_prog p\<^sub>j (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs)) ys,
                           is\<^sub>j',
                           \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs)),(),
		           \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j') ],
                  flush ys ?m_A, share ys ?share_A)"
		 (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
		 by (auto)

	       note conflict_computation = rtranclp_trans [OF rtranclp_r_rtranclp [OF steps_flush_sb, OF store_step] steps_ys]
	       from cph
	       have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ((ys @ [Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W']) @ zs)"
		 by simp
	       from causal_program_history_suffix [OF this]
	       have cph': "causal_program_history is\<^sub>s\<^sub>b\<^sub>j zs".	      
	       interpret causal\<^sub>j: causal_program_history "is\<^sub>s\<^sub>b\<^sub>j" "zs" by (rule cph')

	       from causal\<^sub>j.causal_program_history [of "[]", simplified, OF refl] is\<^sub>j'   
	       obtain is\<^sub>j''
		 where is\<^sub>j': "is\<^sub>j' = Write True a'' sop' A' L' R' W'#is\<^sub>j''" and
		 is\<^sub>j'': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j'' @ prog_instrs zs"
		 by clarsimp
	       
	       from j_bound'''
	       have j_bound_ys: "j < length ?ts_ys"
		 by auto

	       from j_bound_ys neq_i_j
	       have ts_ys_j: "?ts_ys!j=(last_prog (hd_prog p\<^sub>j (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W'# zs)) ys, is\<^sub>j',
                 \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W'# zs)),(),\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {},
                 acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')"
		 by auto

	       from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	       have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	    
	       from safe_delayedE [OF this j_bound_ys ts_ys_j, simplified is\<^sub>j']
	       have A'_unowned: 
		 "\<forall>i < length ?ts_ys. j\<noteq>i \<longrightarrow> (let (\<O>\<^sub>i) = map owned ?ts_ys!i in A' \<inter>  \<O>\<^sub>i = {})"
		 apply cases
		 apply (fastforce simp add: Let_def is\<^sub>s\<^sub>b)+
		 done
	       from a'_in a'_A' A'_unowned [rule_format, of i] neq_i_j i_bound' A_R
	       show False
		 by (auto simp add: Let_def)
	     next
	       assume "\<exists>A L R W ys zs. 
                 suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A L R W # zs \<and> a' \<in> A" 
	       then
	       obtain ys zs A' L' R' W' where
		  split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs" (is "suspends\<^sub>j = ?suspends") and
		 a'_A': "a' \<in> A'"
		 by auto
		 
	       from direct_memop_step.WriteVolatile [where  \<theta>=\<theta>\<^sub>s\<^sub>b and m="flush ?drop_sb m"]
	       have "(Write True a (D, f) A L R W# is\<^sub>s\<^sub>b', 
                          \<theta>\<^sub>s\<^sub>b, (), flush ?drop_sb m,\<D>\<^sub>s\<^sub>b,acquired True sb \<O>\<^sub>s\<^sub>b, 
                          release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b,
                         share ?drop_sb \<S>) \<rightarrow> 
                    (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), (flush ?drop_sb m)(a := f \<theta>\<^sub>s\<^sub>b), True, acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R, Map.empty, 
                      share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

	       from direct_computation.concurrent_step.Memop [OF 
		 i_bound_ts' [simplified is\<^sub>s\<^sub>b] ts'_i [simplified is\<^sub>s\<^sub>b] this [simplified is\<^sub>s\<^sub>b]] 
	       have store_step: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>) \<Rightarrow>\<^sub>d 
                   (?ts'[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', 
		         \<theta>\<^sub>s\<^sub>b, (), True, acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)], 
                         (flush ?drop_sb m)(a := f \<theta>\<^sub>s\<^sub>b),share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		   (is " _ \<Rightarrow>\<^sub>d (?ts_A, ?m_A, ?share_A)")
		 by (simp add: is\<^sub>s\<^sub>b)
	      
	       
	       from i_bound' have i_bound'': "i < length ?ts_A"
		 by simp

	       from valid_program_history [OF j_bound'' ts\<^sub>s\<^sub>b_j] 
	       have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	       then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
		 apply -
		 apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		 apply (simp add: split_suspends\<^sub>j)
		 done
	       
	       from ts\<^sub>j neq_i_j j_bound 
	       have ts_A_j: "?ts_A!j = (hd_prog p\<^sub>j (ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs), is\<^sub>j, 
		 \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)), (),\<D>\<^sub>j, 
		 acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
		 by (simp add: split_suspends\<^sub>j)


	       from j_bound''' i_bound' neq_i_j have j_bound'''': "j < length ?ts_A"
		 by simp
	       
	       from valid_last_prog [OF j_bound'' ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	       then
	       have lp: "last_prog p\<^sub>j ?suspends = p\<^sub>j"
		 apply -
		 apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		 apply simp
		 done
	       
	       from valid_reads [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have reads_consis: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	       
	       from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> 
		 j_bound''
		 ts\<^sub>s\<^sub>b_j reads_consis]
	       have reads_consis_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
		 by (simp add: m suspends\<^sub>j)
	       
	       from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound'' neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j]
	       have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
		 by (simp add: suspends\<^sub>j)
	       from reads_consistent_flush_independent [OF this reads_consis_m]
	       have reads_consis_flush_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
		 (flush ?drop_sb m) suspends\<^sub>j".       

	       from a_unowned_others [rule_format, OF _ neq_i_j] j_bound ts\<^sub>s\<^sub>b_j
	       obtain a_notin_owns_j: "a \<notin> acquired True ?take_sb\<^sub>j \<O>\<^sub>j" and a_unshared: "a \<notin> all_shared ?take_sb\<^sub>j"
	         by auto
	       from a_not_acquired_others [rule_format, OF _ neq_i_j] j_bound ts\<^sub>s\<^sub>b_j
	       have a_not_acquired_j: "a \<notin> all_acquired sb\<^sub>j"
		 by auto
	       
	       from outstanding_non_volatile_refs_owned_or_read_only [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have nvo_j: "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".

	       have a_no_non_vol_read: "a \<notin> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?drop_sb\<^sub>j"
	       proof 
		 assume a_in_nvr:"a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?drop_sb\<^sub>j"
		 
		 from reads_consistent_drop [OF reads_consis]
		 have rc: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) (flush ?take_sb\<^sub>j m\<^sub>s\<^sub>b) ?drop_sb\<^sub>j".

		 from non_volatile_owned_or_read_only_drop [OF nvo_j]
		 have nvo_j_drop: "non_volatile_owned_or_read_only True (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)
		   (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)
		   ?drop_sb\<^sub>j"
		   by simp
		 
		 from outstanding_refs_non_volatile_Read\<^sub>s\<^sub>b_all_acquired [OF rc this a_in_nvr]
		 
		 have a_owns_acq_ror: 
		   "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j \<union> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
		   by (auto dest!: acquired_all_acquired_in all_acquired_takeWhile_dropWhile_in
		     simp add: acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)
		 
		 have a_unowned_j: "a \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
                 proof (cases "a \<in> \<O>\<^sub>j")
                   case False with a_not_acquired_j show ?thesis by auto
                 next
                   case True
                   from all_shared_acquired_in [OF True a_unshared] a_notin_owns_j
                   have False by auto thus ?thesis ..
                 qed
		 
		 with a_owns_acq_ror 
		 have a_ror: "a \<in> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
		   by auto
		 
		 with read_only_reads_unowned [OF j_bound'' i_bound neq_i_j [symmetric] ts\<^sub>s\<^sub>b_j ts\<^sub>s\<^sub>b_i]
		 have a_unowned_sb: "a \<notin> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
		   by auto
		 
		 from sharing_consis [OF j_bound'' ts\<^sub>s\<^sub>b_j] sharing_consistent_append [of \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		 have consis_j_drop: "sharing_consistent (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b) (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
		   by auto
		 
		 from read_only_reads_read_only [OF nvo_j_drop consis_j_drop] a_ror a_unowned_j
		   all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j] acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b [of sb\<^sub>j \<O>\<^sub>j]
		 have "a \<in> read_only (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
		   by (auto)
		 from read_only_share_all_shared [OF this] a_unshared
		 have "a \<in> read_only \<S>\<^sub>s\<^sub>b"
		   by fastforce
		 
		 from read_only_unacquired_share [OF read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] 
		   weak_sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i] this] a_unowned_sb
		 have "a \<in> read_only (share sb \<S>\<^sub>s\<^sub>b)"
		   by auto
		 
		 with a_not_ro show False
		   by simp
	       qed
	 
	 
	       with reads_consistent_mem_eq_on_non_volatile_reads  [OF _ subset_refl reads_consis_flush_m]
	       have "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?m_A suspends\<^sub>j"
		 by (auto simp add: suspends\<^sub>j)
	       

	       hence reads_consis_m_A_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?m_A ys"
		 by (simp add: split_suspends\<^sub>j reads_consistent_append)       

	       from valid_history [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have h_consis: 
		 "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		 apply simp
		 done
	       
	       have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	       proof -
		 from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		   by simp
		 from last_prog_hd_prog_append' [OF h_consis] this
		 have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		   by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		 moreover 
		 have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		   last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		   apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		   by (rule last_prog_hd_prog_append)
		 ultimately show ?thesis
		   by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	       qed
	       
	       from valid_write_sops [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
		 by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	       then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		   valid_sops_drop: "\<forall>sop\<in>write_sops ys. valid_sop sop"
		 apply (simp only: write_sops_append )
		 apply auto
		 done
	       
	       from read_tmps_distinct [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
		 by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	       then obtain 
		 read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
		 distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		 apply (simp only: distinct_read_tmps_append)
		 done
	       
	       from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop h_consis]	  
		 last_prog_hd_prog
	       have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
		 by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	       from reads_consistent_drop_volatile_writes_no_volatile_reads  
	       [OF reads_consis] 
	       have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b ys = {}"
		 by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		   split_suspends\<^sub>j )
	   
	       from flush_store_buffer_append [
		 OF j_bound''''  is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
		 ts_A_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_m_A_ys
		 hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
		 no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
		 \<S>="?share_A"]
	       obtain is\<^sub>j' \<R>\<^sub>j' where
		 is\<^sub>j': "instrs (Ghost\<^sub>s\<^sub>b A' L' R' W' # zs) @ is\<^sub>s\<^sub>b\<^sub>j = 
	            is\<^sub>j' @ prog_instrs (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)" and
		 steps_ys: "(?ts_A, ?m_A, ?share_A)  \<Rightarrow>\<^sub>d\<^sup>* 
		(?ts_A[j:= (last_prog (hd_prog p\<^sub>j (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)) ys,
                           is\<^sub>j',
                           \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)),(),
		           \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j') ],
                  flush ys ?m_A,
                  share ys ?share_A)"
		 (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
		 by (auto)

	       note conflict_computation = rtranclp_trans [OF rtranclp_r_rtranclp [OF steps_flush_sb, OF store_step] steps_ys]
	       from cph
	       have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ((ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W']) @ zs)"
		 by simp
	       from causal_program_history_suffix [OF this]
	       have cph': "causal_program_history is\<^sub>s\<^sub>b\<^sub>j zs".	      
	       interpret causal\<^sub>j: causal_program_history "is\<^sub>s\<^sub>b\<^sub>j" "zs" by (rule cph')

	       from causal\<^sub>j.causal_program_history [of "[]", simplified, OF refl] is\<^sub>j'   
	       obtain is\<^sub>j''
		 where is\<^sub>j': "is\<^sub>j' = Ghost A' L' R' W'#is\<^sub>j''" and
		 is\<^sub>j'': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j'' @ prog_instrs zs"
		 by clarsimp
	       
	       from j_bound'''
	       have j_bound_ys: "j < length ?ts_ys"
		 by auto

	       from j_bound_ys neq_i_j
	       have ts_ys_j: "?ts_ys!j=(last_prog (hd_prog p\<^sub>j (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)) ys, is\<^sub>j',
                 \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W'# zs)),(),\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {},
                 acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')"
		 by auto

	       from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	       have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	    
	       from safe_delayedE [OF this j_bound_ys ts_ys_j, simplified is\<^sub>j']
	       have A'_unowned: 
		 "\<forall>i < length ?ts_ys. j\<noteq>i \<longrightarrow> (let (\<O>\<^sub>i) = map owned ?ts_ys!i in A' \<inter>  \<O>\<^sub>i = {})"
		 apply cases
		 apply (fastforce simp add: Let_def is\<^sub>s\<^sub>b)+
		 done
	       from a'_in a'_A' A'_unowned [rule_format, of i] neq_i_j i_bound' A_R
	       show False
		 by (auto simp add: Let_def)
	     qed
	   qed
	 qed
       }
       thus ?thesis
	 by (auto simp add: Let_def)
      qed

      have A_no_read_only_reads_by_others:
	  "\<forall>j<length (map \<O>_sb ts\<^sub>s\<^sub>b). i \<noteq> j \<longrightarrow>
             (let (\<O>\<^sub>j, sb\<^sub>j) = map \<O>_sb ts\<^sub>s\<^sub>b! j
             in A \<inter> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j)
	             (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) = {})"
      proof -
	{
	  fix j \<O>\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length (map \<O>_sb ts\<^sub>s\<^sub>b)"
	  assume neq_i_j: "i\<noteq>j"
	  assume ts\<^sub>s\<^sub>b_j: "(map \<O>_sb ts\<^sub>s\<^sub>b)!j = (\<O>\<^sub>j,sb\<^sub>j)"
	  let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	  let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"

	  assume conflict: "A \<inter> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j  \<noteq> {}"
	  have False
	  proof -
	    from j_bound leq
	    have j_bound': "j < length (map owned ts)"
	      by auto
	    from j_bound have j_bound'': "j < length ts\<^sub>s\<^sub>b"
	      by auto
	    from j_bound' have j_bound''': "j < length ts"
	      by simp
	    
	    from conflict obtain a' where
	      a'_in: "a' \<in> A" and
              a'_in_j: "a' \<in> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
	      by auto


	    from ts_sim [rule_format, OF  j_bound''] ts\<^sub>s\<^sub>b_j j_bound''
	    obtain p\<^sub>j suspends\<^sub>j "is\<^sub>s\<^sub>b\<^sub>j" \<D>\<^sub>s\<^sub>b\<^sub>j \<D>\<^sub>j \<R>\<^sub>j \<theta>\<^sub>s\<^sub>b\<^sub>j "is\<^sub>j" where
	      ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j, \<theta>\<^sub>s\<^sub>b\<^sub>j, sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
	      suspends\<^sub>j: "suspends\<^sub>j = ?drop_sb\<^sub>j" and
	      is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
	      \<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
	      ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
	             \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	      apply (cases "ts\<^sub>s\<^sub>b!j")
	      apply (force simp add: Let_def)
	      done
	      

	    from split_in_read_only_reads [OF a'_in_j [simplified suspends\<^sub>j [symmetric]]]
	    obtain t v ys zs where
	      split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Read\<^sub>s\<^sub>b False a' t v# zs" (is "suspends\<^sub>j = ?suspends") and
	      a'_unacq: "a' \<notin> acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)"
	      by blast
	    
	    from direct_memop_step.WriteVolatile [where  \<theta>=\<theta>\<^sub>s\<^sub>b and m="flush ?drop_sb m"]
	    have "(Write True a (D, f) A L R W# is\<^sub>s\<^sub>b', 
                  \<theta>\<^sub>s\<^sub>b, (), flush ?drop_sb m, \<D>\<^sub>s\<^sub>b,acquired True sb \<O>\<^sub>s\<^sub>b, 
                  release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b, share ?drop_sb \<S>) \<rightarrow> 
                    (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), (flush ?drop_sb m)(a := f \<theta>\<^sub>s\<^sub>b), True, acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty, 
                      share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

	    from direct_computation.concurrent_step.Memop [OF 
	      i_bound_ts' [simplified is\<^sub>s\<^sub>b] ts'_i [simplified is\<^sub>s\<^sub>b] this [simplified is\<^sub>s\<^sub>b]] 
	    have store_step: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>) \<Rightarrow>\<^sub>d 
                    (?ts'[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), 
                         True, acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)], 
                         (flush ?drop_sb m)(a := f \<theta>\<^sub>s\<^sub>b),share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		  (is " _ \<Rightarrow>\<^sub>d (?ts_A, ?m_A, ?share_A)")
	     by (simp add: is\<^sub>s\<^sub>b)
	      
	       
	   from i_bound' have i_bound'': "i < length ?ts_A"
	     by simp

	   from valid_program_history [OF j_bound'' ts\<^sub>s\<^sub>b_j] 
	   have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	   then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
	     apply -
	     apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
	     apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	     apply (simp add: split_suspends\<^sub>j)
	     done
	   
	   from ts\<^sub>j neq_i_j j_bound 
	   have ts_A_j: "?ts_A!j = (hd_prog p\<^sub>j (ys @ Read\<^sub>s\<^sub>b False a' t v# zs), is\<^sub>j,
	     \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (ys @ Read\<^sub>s\<^sub>b False a' t v# zs)), (), \<D>\<^sub>j, 
	     acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	     by (simp add: split_suspends\<^sub>j)


	   from j_bound''' i_bound' neq_i_j have j_bound'''': "j < length ?ts_A"
	     by simp

	   from valid_last_prog [OF j_bound'' ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	   then
	   have lp: "last_prog p\<^sub>j ?suspends = p\<^sub>j"
	     apply -
	     apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
	     apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	     apply simp
	     done

	   from valid_reads [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have reads_consis: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".

	   from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> j_bound''
	     ts\<^sub>s\<^sub>b_j reads_consis]
	   have reads_consis_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
	     by (simp add: m suspends\<^sub>j)

	   from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound'' neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j]
	   have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
	     by (simp add: suspends\<^sub>j)
	   from reads_consistent_flush_independent [OF this reads_consis_m]
	   have reads_consis_flush_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
	     (flush ?drop_sb m) suspends\<^sub>j".

	   from a_unowned_others [rule_format, OF j_bound'' neq_i_j ] j_bound ts\<^sub>s\<^sub>b_j
	   obtain a_notin_owns_j: "a \<notin> acquired True ?take_sb\<^sub>j \<O>\<^sub>j" and a_unshared: "a \<notin> all_shared ?take_sb\<^sub>j"
	     by auto
	   from a_not_acquired_others [rule_format, OF j_bound neq_i_j] j_bound ts\<^sub>s\<^sub>b_j
	   have a_not_acquired_j: "a \<notin> all_acquired sb\<^sub>j"
	     by auto
	   
	   from outstanding_non_volatile_refs_owned_or_read_only [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have nvo_j: "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	   
	   have a_no_non_vol_read: "a \<notin> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?drop_sb\<^sub>j"
	   proof 
	     assume a_in_nvr:"a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?drop_sb\<^sub>j"

	     from reads_consistent_drop [OF reads_consis]
	     have rc: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) (flush ?take_sb\<^sub>j m\<^sub>s\<^sub>b) ?drop_sb\<^sub>j".

	     from non_volatile_owned_or_read_only_drop [OF nvo_j]
	     have nvo_j_drop: "non_volatile_owned_or_read_only True (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)
	       (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)
	       ?drop_sb\<^sub>j"
	       by simp

	     from outstanding_refs_non_volatile_Read\<^sub>s\<^sub>b_all_acquired [OF rc this a_in_nvr]

	     have a_owns_acq_ror: 
	       "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j \<union> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
	       by (auto dest!: acquired_all_acquired_in all_acquired_takeWhile_dropWhile_in
		 simp add: acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)
             
	     have a_unowned_j: "a \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
             proof (cases "a \<in> \<O>\<^sub>j")
               case False with a_not_acquired_j show ?thesis by auto
             next
               case True
               from all_shared_acquired_in [OF True a_unshared] a_notin_owns_j
               have False by auto thus ?thesis ..
             qed
		 
	     with a_owns_acq_ror 
	     have a_ror: "a \<in> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
	       by auto

	     with read_only_reads_unowned [OF j_bound'' i_bound neq_i_j [symmetric] ts\<^sub>s\<^sub>b_j ts\<^sub>s\<^sub>b_i]
	     have a_unowned_sb: "a \<notin> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
	       by auto
	       
	     from sharing_consis [OF j_bound'' ts\<^sub>s\<^sub>b_j] sharing_consistent_append [of \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	     have consis_j_drop: "sharing_consistent (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b) (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
	       by auto

	     from read_only_reads_read_only [OF nvo_j_drop consis_j_drop] a_ror a_unowned_j
	       all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j] acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b [of sb\<^sub>j \<O>\<^sub>j]
	     have "a \<in> read_only (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
	       by (auto)
	     from read_only_share_all_shared [OF this] a_unshared
	     have "a \<in> read_only \<S>\<^sub>s\<^sub>b"
	       by fastforce
	      
	     from read_only_unacquired_share [OF read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] 
	       weak_sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i] this] a_unowned_sb
	     have "a \<in> read_only (share sb \<S>\<^sub>s\<^sub>b)"
	       by auto
	   
	     with a_not_ro show False
	       by simp
	   qed
	 
	   with reads_consistent_mem_eq_on_non_volatile_reads  [OF _ subset_refl reads_consis_flush_m]
	   have "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?m_A suspends\<^sub>j"
	     by (auto simp add: suspends\<^sub>j)


	   hence reads_consis_m_A_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?m_A ys"
	     by (simp add: split_suspends\<^sub>j reads_consistent_append)

	   from valid_history [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have h_consis: 
	     "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
	     apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	     apply simp
	     done

	   have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	   proof -
	     from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
	       by simp
	     from last_prog_hd_prog_append' [OF h_consis] this
	     have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
	       by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	     moreover 
	     have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		  last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
	       apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	       by (rule last_prog_hd_prog_append)
	     ultimately show ?thesis
	       by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	   qed

	   from valid_write_sops [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
	     by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	   then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
	     valid_sops_drop: "\<forall>sop\<in>write_sops ys. valid_sop sop"
	     apply (simp only: write_sops_append )
	     apply auto
	     done

	   from read_tmps_distinct [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
	     by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	   then obtain 
	     read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
	     distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
	     apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	     apply (simp only: distinct_read_tmps_append)
	     done
	   
	   from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop h_consis]	  
	     last_prog_hd_prog
	   have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
	     by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	    from reads_consistent_drop_volatile_writes_no_volatile_reads  
	    [OF reads_consis] 
	    have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b ys = {}"
	      by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		split_suspends\<^sub>j )
	   
	    from flush_store_buffer_append [
	      OF j_bound''''  is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
	      ts_A_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_m_A_ys
	      hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
	      no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
	      \<S>="?share_A"]
	    obtain is\<^sub>j' \<R>\<^sub>j' where
	      is\<^sub>j': "instrs (Read\<^sub>s\<^sub>b False a' t v# zs) @ is\<^sub>s\<^sub>b\<^sub>j = 
	            is\<^sub>j' @ prog_instrs (Read\<^sub>s\<^sub>b False a' t v# zs)" and
	      steps_ys: "(?ts_A, ?m_A, ?share_A)  \<Rightarrow>\<^sub>d\<^sup>* 
		(?ts_A[j:= (last_prog (hd_prog p\<^sub>j (Read\<^sub>s\<^sub>b False a' t v# zs)) ys,
                           is\<^sub>j',
                           \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Read\<^sub>s\<^sub>b False a' t v# zs)),(),
                           \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j') ],
                  flush ys ?m_A,
                  share ys ?share_A)"
		 (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
              by (auto)

	    note conflict_computation = rtranclp_trans [OF rtranclp_r_rtranclp [OF steps_flush_sb, OF store_step] steps_ys]
	    from cph
	    have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ((ys @ [Read\<^sub>s\<^sub>b False a' t v]) @ zs)"
	      by simp
	    from causal_program_history_suffix [OF this]
	    have cph': "causal_program_history is\<^sub>s\<^sub>b\<^sub>j zs".	      
	    interpret causal\<^sub>j: causal_program_history "is\<^sub>s\<^sub>b\<^sub>j" "zs" by (rule cph')

	    from causal\<^sub>j.causal_program_history [of "[]", simplified, OF refl] is\<^sub>j'   
	    obtain is\<^sub>j''
	      where is\<^sub>j': "is\<^sub>j' = Read False a' t#is\<^sub>j''" and
	      is\<^sub>j'': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j'' @ prog_instrs zs"
	      by clarsimp

	    from j_bound'''
	    have j_bound_ys: "j < length ?ts_ys"
	      by auto

	    from j_bound_ys neq_i_j
	    have ts_ys_j: "?ts_ys!j=(last_prog (hd_prog p\<^sub>j (Read\<^sub>s\<^sub>b False a' t v# zs)) ys, is\<^sub>j',
                 \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Read\<^sub>s\<^sub>b False a' t v# zs)),(),
	         \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {},
                 acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')"
	      by auto

	    from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	    have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	    
	    from safe_delayedE [OF this j_bound_ys ts_ys_j, simplified is\<^sub>j']
	    have "a' \<in> acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<or>
                  a' \<in> read_only (share ys (share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
	      apply cases
	      apply (auto simp add: Let_def is\<^sub>s\<^sub>b)
	      done
	    with a'_unacq
	    have a'_ro: "a' \<in> read_only (share ys (share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
	      by auto
	    from a'_in
	    have a'_not_ro: "a' \<notin> read_only (share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	      by (auto simp add:  in_read_only_convs)

	    have "a' \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	    proof -
	      {
		assume a_notin: "a' \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
		from weak_sharing_consis [OF j_bound'' ts\<^sub>s\<^sub>b_j]
		have "weak_sharing_consistent \<O>\<^sub>j sb\<^sub>j".
		with weak_sharing_consistent_append [of \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		have "weak_sharing_consistent (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) suspends\<^sub>j"
		  by (auto simp add: suspends\<^sub>j)
                
		with split_suspends\<^sub>j
		have weak_consis: "weak_sharing_consistent (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ys"
		  by (simp add: weak_sharing_consistent_append)
		from all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		have "all_acquired ys \<subseteq> all_acquired sb\<^sub>j"
		  apply (clarsimp)
		  apply (clarsimp simp add: suspends\<^sub>j [symmetric] split_suspends\<^sub>j all_acquired_append)
		  done

                with a_notin acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b [of sb\<^sub>j \<O>\<^sub>j]
                  all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		have "a' \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j \<union> all_acquired ys"
                  by auto
                
		from read_only_share_unowned [OF weak_consis this a'_ro] 
		have "a' \<in> read_only (share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" .
		  
		with a'_not_ro have False
		  by auto
	      }
	      thus ?thesis by blast
	    qed
		
	    moreover
	    from A_unaquired_by_others [rule_format, OF j_bound neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
	    have "A \<inter> all_acquired sb\<^sub>j = {}"
	      by (auto simp add: Let_def)
	    moreover
	    from A_unowned_by_others [rule_format, OF j_bound'' neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
	    have "A \<inter> \<O>\<^sub>j = {}"
	      by (auto simp add: Let_def dest: all_shared_acquired_in)
	    moreover note a'_in
	    ultimately
	    show False
	      by auto
	  qed
	}
	thus ?thesis
	  by (auto simp add: Let_def)
      qed

      have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof -
	  from outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i] 
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb @ [Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W]) "
	    by (auto simp add: non_volatile_owned_or_read_only_append)
	  from outstanding_non_volatile_refs_owned_or_read_only_nth_update [OF i_bound this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	qed
      next
	show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)
	  fix i\<^sub>1 j p\<^sub>1 "is\<^sub>1" \<O>\<^sub>1 \<R>\<^sub>1 \<D>\<^sub>1 xs\<^sub>1 sb\<^sub>1 p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume i\<^sub>1_bound: "i\<^sub>1 < length ts\<^sub>s\<^sub>b'"
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume i\<^sub>1_j: "i\<^sub>1 \<noteq> j"
	  assume ts_i\<^sub>1: "ts\<^sub>s\<^sub>b'!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	  assume ts_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}"
	  proof (cases "i\<^sub>1=i")
	    case True
	    with i\<^sub>1_j have i_j: "i\<noteq>j" 
	      by simp
	    
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    hence j_bound'': "j < length (map owned ts\<^sub>s\<^sub>b)"
	      by simp
	    from ts_j i_j have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    from a_unowned_others [rule_format, OF _ i_j] i_j ts_j j_bound
	    obtain a_notin_j: "a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j" and
              a_unshared: "a \<notin> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	      by (auto simp add: Let_def ts\<^sub>s\<^sub>b')
	    from a_not_acquired_others [rule_format, OF _ i_j] i_j ts_j j_bound
	    have a_notin_acq: "a \<notin> all_acquired sb\<^sub>j"
	      by (auto simp add: Let_def ts\<^sub>s\<^sub>b')
	    from outstanding_volatile_writes_unowned_by_others 
	    [OF i_bound j_bound' i_j ts\<^sub>s\<^sub>b_i ts_j']
	    have "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}".
	    with ts_i\<^sub>1 a_notin_j a_unshared a_notin_acq True i_bound show ?thesis
	      by (auto simp add: ts\<^sub>s\<^sub>b' sb' outstanding_refs_append 
		acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b dest: all_shared_acquired_in)
	  next
	    case False
	    note i\<^sub>1_i = this
	    from i\<^sub>1_bound have i\<^sub>1_bound': "i\<^sub>1 < length ts\<^sub>s\<^sub>b"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    from ts_i\<^sub>1 False have ts_i\<^sub>1': "ts\<^sub>s\<^sub>b!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    show ?thesis
	    proof (cases "j=i")
	      case True

	      from i\<^sub>1_bound'
	      have i\<^sub>1_bound'': "i\<^sub>1 < length (map owned ts\<^sub>s\<^sub>b)"
		by simp

	      from outstanding_volatile_writes_unowned_by_others 
	      [OF i\<^sub>1_bound' i_bound i\<^sub>1_i ts_i\<^sub>1' ts\<^sub>s\<^sub>b_i]
	      have "(\<O>\<^sub>s\<^sub>b \<union> all_acquired sb) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}".
	      moreover
	      from A_unused_by_others [rule_format, OF _ False [symmetric]] False ts_i\<^sub>1 i\<^sub>1_bound
	      have "A \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}"
		by (auto simp add: Let_def ts\<^sub>s\<^sub>b')
	      
	      ultimately
	      show ?thesis
		using ts_j True ts\<^sub>s\<^sub>b' 
		by (auto simp add: i_bound ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' all_acquired_append)
	    next
	      case False
	      from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from ts_j False have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from outstanding_volatile_writes_unowned_by_others 
              [OF i\<^sub>1_bound' j_bound' i\<^sub>1_j ts_i\<^sub>1' ts_j']
	      show "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}" .
	    qed
	  qed
	qed
      next
	show "ownership_distinct ts\<^sub>s\<^sub>b'"
	proof -
	  have "\<forall>j<length ts\<^sub>s\<^sub>b. i \<noteq> j \<longrightarrow>
	    (let (p\<^sub>j, is\<^sub>j, \<theta>\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j,\<R>\<^sub>j) = ts\<^sub>s\<^sub>b ! j
	      in (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb') \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {})"
	  proof -
	    {
	      fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j acq\<^sub>j \<theta>\<^sub>j sb\<^sub>j
	      assume neq_i_j: "i \<noteq> j"
	      assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	      assume ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j, is\<^sub>j, \<theta>\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j,\<R>\<^sub>j)"
	      have "(\<O>\<^sub>s\<^sub>b \<union> all_acquired sb') \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {}"
	      proof -
		{
		  fix a'
		  assume a'_in_i: "a' \<in> (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb')"
		  assume a'_in_j: "a' \<in> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j)"
		  have False
		  proof -
		    from a'_in_i have "a' \<in> (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb) \<or> a' \<in> A"
		      by (simp add: sb' all_acquired_append)
		    then show False
		    proof 
		      assume "a' \<in> (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb)"
		      with ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j] a'_in_j
		      show ?thesis
			by auto
		    next
		      assume "a' \<in> A"
		      moreover
		      have j_bound': "j < length (map owned ts\<^sub>s\<^sub>b)"
			using j_bound by auto
		      from A_unowned_by_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
		      obtain "A \<inter> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j = {}" and
                             "A \<inter> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) = {}"
			by (auto simp add: Let_def)
		      moreover
		      from A_unaquired_by_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
		      have "A \<inter> all_acquired sb\<^sub>j = {}"
			by auto
		      ultimately
		      show ?thesis
			using a'_in_j
			by (auto dest: all_shared_acquired_in)
		    qed
		  qed
		}
		then show ?thesis by auto
	      qed
	    }
	    then show ?thesis by (fastforce simp add: Let_def)
	  qed
	
	  from ownership_distinct_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb')
	qed
      next
	show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
	proof 
	  fix n m
	  fix p\<^sub>n "is\<^sub>n" \<O>\<^sub>n \<R>\<^sub>n \<D>\<^sub>n \<theta>\<^sub>n sb\<^sub>n p\<^sub>m "is\<^sub>m" \<O>\<^sub>m \<R>\<^sub>m \<D>\<^sub>m \<theta>\<^sub>m sb\<^sub>m
	  assume n_bound: "n < length ts\<^sub>s\<^sub>b'"
	    and m_bound: "m < length ts\<^sub>s\<^sub>b'"
	    and neq_n_m: "n\<noteq>m"
	    and nth: "ts\<^sub>s\<^sub>b'!n = (p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
	    and mth: "ts\<^sub>s\<^sub>b'!m =(p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m,\<R>\<^sub>m)"
	  from n_bound have n_bound': "n < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')
	  from m_bound have m_bound': "m < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')
	  
	  show "(\<O>\<^sub>m \<union> all_acquired sb\<^sub>m) \<inter>
            read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) \<O>\<^sub>n)
            (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) =
            {}"
	  proof (cases "m=i")
	    case True
	    with neq_n_m have neq_n_i: "n\<noteq>i"
	      by auto
	    with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    note read_only_reads_unowned [OF n_bound' i_bound  neq_n_i nth' ts\<^sub>s\<^sub>b_i]
	    moreover
	    from A_no_read_only_reads_by_others [rule_format, OF _ neq_n_i [symmetric]] n_bound' nth'
	    have "A \<inter> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) \<O>\<^sub>n)
              (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) =
              {}"
	      by auto
	    ultimately 
	    show ?thesis
	      using True ts\<^sub>s\<^sub>b_i nth' mth n_bound' m_bound'
	      by (auto simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' all_acquired_append)
	  next
	    case False
	    note neq_m_i = this
	    with m_bound mth i_bound have mth': "ts\<^sub>s\<^sub>b!m = (p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m,\<R>\<^sub>m)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    show ?thesis
	    proof (cases "n=i")
	      case True
	      note read_only_reads_unowned [OF i_bound m_bound' neq_m_i [symmetric] ts\<^sub>s\<^sub>b_i mth']
	      then show ?thesis
		using True neq_m_i ts\<^sub>s\<^sub>b_i nth mth n_bound' m_bound'
		apply (case_tac "outstanding_refs (is_volatile_Write\<^sub>s\<^sub>b) sb = {}")
		apply (clarsimp simp add: outstanding_vol_write_take_drop_appends
		  acquired_append read_only_reads_append ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b')+
		done
	    next
	      case False
	      with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      from read_only_reads_unowned [OF n_bound' m_bound' neq_n_m  nth' mth'] False neq_m_i
	      show ?thesis 
		by (clarsimp)
	    qed
	  qed
	qed
      qed	  

      have valid_hist': "valid_history program_step ts\<^sub>s\<^sub>b'"
      proof -
	from valid_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b sb) sb".
	with valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i] D_subset 
	  valid_implies_valid_prog_hd [OF i_bound ts\<^sub>s\<^sub>b_i valid]
	have "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b (sb@[Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])) 
	         (sb@ [Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])"
	  apply -
	  apply (rule history_consistent_appendI)
	  apply (auto simp add: hd_prog_append_Write\<^sub>s\<^sub>b)
	  done
	from valid_history_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<theta>\<^sub>s\<^sub>b')
      qed

      have valid_reads': "valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b'"
      proof -
	from valid_reads [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b sb" .
	from reads_consistent_snoc_Write\<^sub>s\<^sub>b [OF this]
	have "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b (sb @ [Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])".
	from valid_reads_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b')
      qed

      have valid_sharing': "valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)	
	from outstanding_non_volatile_writes_unshared [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b (sb @ [Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])"
	  by (auto simp add: non_volatile_writes_unshared_append)
	from outstanding_non_volatile_writes_unshared_nth_update [OF i_bound this]
	show "outstanding_non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' sb' \<S>\<^sub>s\<^sub>b')
      next
	from sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]
	have consis': "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb".
	from  A_shared_owned
	have "A \<subseteq> dom (share ?drop_sb \<S>) \<union> acquired True sb \<O>\<^sub>s\<^sub>b"
	  by (simp add:  sharing_consistent_append  acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)
	moreover have "dom (share ?drop_sb \<S>) \<subseteq> dom \<S> \<union> dom (share sb \<S>\<^sub>s\<^sub>b)"
	proof
	  fix a'
	  assume a'_in: "a' \<in> dom (share ?drop_sb \<S>)" 
	  from share_unshared_in [OF a'_in]
	  show "a' \<in> dom \<S> \<union> dom (share sb \<S>\<^sub>s\<^sub>b)"
	  proof 
	    assume "a' \<in> dom (share ?drop_sb Map.empty)" 
	    from share_mono_in [OF this] share_append [of ?take_sb ?drop_sb]
	    have "a' \<in> dom (share sb \<S>\<^sub>s\<^sub>b)"
	      by auto
	    thus ?thesis
	      by simp
	  next
	    assume "a' \<in> dom \<S> \<and> a' \<notin> all_unshared ?drop_sb"
	    thus ?thesis by auto
	  qed
	qed
	ultimately
	have A_subset: "A \<subseteq> dom \<S> \<union> dom (share sb \<S>\<^sub>s\<^sub>b) \<union> acquired True sb \<O>\<^sub>s\<^sub>b"
	  by auto

        with A_unowned_by_others 
        
        have "A \<subseteq> dom (share sb \<S>\<^sub>s\<^sub>b) \<union> acquired True sb \<O>\<^sub>s\<^sub>b"
        proof -
          {
            fix x
            assume x_A: "x \<in> A"
            have "x \<in> dom (share sb \<S>\<^sub>s\<^sub>b) \<union> acquired True sb \<O>\<^sub>s\<^sub>b"
            proof -
              {
                assume "x \<in> dom \<S>"
                
                from share_all_until_volatile_write_share_acquired [OF \<open>sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> 
                  i_bound ts\<^sub>s\<^sub>b_i this [simplified \<S>]]
                  A_unowned_by_others x_A
                have ?thesis
                by (fastforce simp add: Let_def)
             }
             with A_subset show ?thesis using x_A by auto
           qed
         }
         thus ?thesis by blast
        qed
	with consis' L_subset A_R R_acq
	have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb @ [Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])"
	  by (simp add:  sharing_consistent_append  acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)
	from sharing_consis_nth_update [OF i_bound this]
	show "sharing_consis \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' \<S>\<^sub>s\<^sub>b')
      next
	from read_only_unowned_nth_update [OF i_bound read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] ]
	show "read_only_unowned \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b')
      next
	from unowned_shared_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i subset_refl]
	show "unowned_shared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next
	from a_not_ro no_outstanding_write_to_read_only_memory [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b (sb @ [Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])"
	  by (simp add: no_write_to_read_only_memory_append)
	
	from no_outstanding_write_to_read_only_memory_nth_update [OF i_bound this]
	show "no_outstanding_write_to_read_only_memory \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb')
      qed

      have tmps_distinct': "tmps_distinct ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_load_tmps is\<^sub>s\<^sub>b'" by (simp add: "is\<^sub>s\<^sub>b")
	from load_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b')
      next
	from read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_read_tmps (sb @ [Write\<^sub>s\<^sub>b True a (D, f) (f \<theta>\<^sub>s\<^sub>b) A L R W])"
	  by (auto simp add: distinct_read_tmps_append)
	from read_tmps_distinct_nth_update [OF i_bound this]
	show "read_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb')
      next
	from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> read_tmps (sb @ [Write\<^sub>s\<^sub>b True a (D, f) (f \<theta>\<^sub>s\<^sub>b) A L R W]) ={}"
	  by (auto simp add: read_tmps_append "is\<^sub>s\<^sub>b")
	from load_tmps_read_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_read_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed
      
      have valid_sops': "valid_sops ts\<^sub>s\<^sub>b'"
      proof -
	from valid_store_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	obtain valid_Df: "valid_sop (D,f)" and  
	  valid_store_sops': "\<forall>sop\<in>store_sops is\<^sub>s\<^sub>b'. valid_sop sop"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	from valid_Df valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	have valid_write_sops': "\<forall>sop\<in>write_sops (sb@ [Write\<^sub>s\<^sub>b True a (D, f) (f \<theta>\<^sub>s\<^sub>b) A L R W]). 
	  valid_sop sop"
	  by (auto simp add: write_sops_append)
	from valid_sops_nth_update [OF i_bound  valid_write_sops' valid_store_sops']
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      have valid_dd': "valid_data_dependency ts\<^sub>s\<^sub>b'"
      proof -
	from data_dependency_consistent_instrs [OF i_bound ts\<^sub>s\<^sub>b_i]
	obtain D_indep: "D \<inter> load_tmps is\<^sub>s\<^sub>b' = {}" and 
	  dd_is: "data_dependency_consistent_instrs (dom \<theta>\<^sub>s\<^sub>b') is\<^sub>s\<^sub>b'"
	  by (auto simp add: "is\<^sub>s\<^sub>b" \<theta>\<^sub>s\<^sub>b')
	from load_tmps_write_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] D_indep
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> \<Union>(fst ` write_sops (sb@ [Write\<^sub>s\<^sub>b True a (D, f) (f \<theta>\<^sub>s\<^sub>b) A L R W])) ={}"
	  by (auto simp add: write_sops_append "is\<^sub>s\<^sub>b")
	from valid_data_dependency_nth_update [OF i_bound dd_is this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      have load_tmps_fresh': "load_tmps_fresh ts\<^sub>s\<^sub>b'"
      proof -
	from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> dom \<theta>\<^sub>s\<^sub>b = {}"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	from load_tmps_fresh_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
      qed

      have enough_flushs': "enough_flushs ts\<^sub>s\<^sub>b'"
      proof -
	from clean_no_outstanding_volatile_Write\<^sub>s\<^sub>b [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "\<not> True \<longrightarrow> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W]) = {}"
	  by (auto simp add: outstanding_refs_append )
	from enough_flushs_nth_update [OF i_bound this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' sb' \<D>\<^sub>s\<^sub>b')
      qed

      have valid_program_history': "valid_program_history ts\<^sub>s\<^sub>b'"
      proof -	
	from valid_program_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "causal_program_history is\<^sub>s\<^sub>b sb" .
	then have causal': "causal_program_history is\<^sub>s\<^sub>b' (sb@[Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W])"
	  by (auto simp: causal_program_history_Write  "is\<^sub>s\<^sub>b")
	from valid_last_prog [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "last_prog p\<^sub>s\<^sub>b sb = p\<^sub>s\<^sub>b".
	hence "last_prog p\<^sub>s\<^sub>b (sb @ [Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W]) = p\<^sub>s\<^sub>b"
	  by (simp add: last_prog_append_Write\<^sub>s\<^sub>b)
	from valid_program_history_nth_update [OF i_bound causal' this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      show ?thesis
      proof (cases "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}")
	case True
	
	from True have flush_all: "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = sb"
	  by (auto simp add: outstanding_refs_conv)
	
	from True have suspend_nothing: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = []"
	  by (auto simp add: outstanding_refs_conv)

	hence suspends_empty: "suspends = []"
	  by (simp add: suspends)

	from suspends_empty is_sim have "is": "is = Write True a (D,f) A L R W# is\<^sub>s\<^sub>b'"
	  by (simp add: "is\<^sub>s\<^sub>b")
	with suspends_empty ts_i 
	have ts_i: "ts!i = (p\<^sub>s\<^sub>b, Write True a (D,f) A L R W# is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b,(),\<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b, release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
	  by simp

	have "(ts, m, \<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts, m, \<S>)" by auto

	moreover
	
	note flush_commute =
	  flush_all_until_volatile_write_append_volatile_write_commute 
	[OF True i_bound ts\<^sub>s\<^sub>b_i]


	from True 
	have drop_app: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) 
	  (sb@[Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W]) =
          [Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>\<^sub>s\<^sub>b) A L R W]"
	  by (auto simp add: outstanding_refs_conv)

	have "(ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> (ts,m,\<S>)"
	  apply (rule sim_config.intros) 
	  apply    (simp add: m flush_commute ts\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' sb') 	  
	  using  share_all_until_volatile_write_Write_commute 
	          [OF i_bound ts\<^sub>s\<^sub>b_i [simplified is\<^sub>s\<^sub>b]]
	  apply   (clarsimp simp add: \<S> \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
	  using  leq
	  apply  (simp add: ts\<^sub>s\<^sub>b')
	  using i_bound i_bound' ts_sim ts_i 
	  apply (clarsimp simp add: Let_def nth_list_update drop_app (* drop*) 
	    ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' \<D>\<^sub>s\<^sub>b'  outstanding_refs_append takeWhile_tail flush_all
	    split: if_split_asm )
	  done

	ultimately show ?thesis
	  using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' 
	    valid_sops'
            valid_dd' load_tmps_fresh' enough_flushs' 
	    valid_program_history' valid' m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b'
	  by auto
      next
	case False

	then obtain r where r_in: "r \<in> set sb" and volatile_r: "is_volatile_Write\<^sub>s\<^sub>b r"
	  by (auto simp add: outstanding_refs_conv)
	from takeWhile_dropWhile_real_prefix 
	[OF r_in, of  "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)", simplified, OF volatile_r] 
	obtain a' v' sb'' A'' L'' R'' W'' sop' where
	  sb_split: "sb = takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb @ Write\<^sub>s\<^sub>b True a' sop' v' A'' L'' R'' W''# sb''" 
	  and
	  drop: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = Write\<^sub>s\<^sub>b True a' sop' v' A'' L'' R'' W''# sb''"
	  apply (auto)
    subgoal for y ys
	  apply (case_tac y)
	  apply auto
	  done
	  done
	from drop suspends have suspends: "suspends = Write\<^sub>s\<^sub>b True a' sop' v' A'' L'' R'' W''# sb''"
	  by simp

	have "(ts, m, \<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts, m, \<S>)" by auto
	
	moreover

	note flush_commute =
	  flush_all_until_volatile_write_append_unflushed [OF False i_bound ts\<^sub>s\<^sub>b_i]

	have "Write\<^sub>s\<^sub>b True a' sop' v' A'' L'' R'' W'' \<in> set sb"
	  by (subst sb_split) auto
	note drop_app = dropWhile_append1 
	[OF this, of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)", simplified]

	have "(ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> (ts,m,\<S>)"
	  apply (rule sim_config.intros) 
	  apply    (simp add: m flush_commute ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb')
	  using  share_all_until_volatile_write_Write_commute 
	          [OF i_bound ts\<^sub>s\<^sub>b_i [simplified is\<^sub>s\<^sub>b]]
	  apply   (clarsimp simp add: \<S> \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
	  using  leq
	  apply  (simp add: ts\<^sub>s\<^sub>b')
	  using i_bound i_bound' ts_sim ts_i is_sim 
	  apply (clarsimp simp add: Let_def nth_list_update is_sim drop_app
	    read_tmps_append suspends 
	    prog_instrs_append_Write\<^sub>s\<^sub>b instrs_append_Write\<^sub>s\<^sub>b hd_prog_append_Write\<^sub>s\<^sub>b
	    drop "is\<^sub>s\<^sub>b" ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' \<D>\<^sub>s\<^sub>b' outstanding_refs_append takeWhile_tail release_append split: if_split_asm)
	  done
	ultimately show ?thesis
	  using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' valid_dd'
	    valid_sops' load_tmps_fresh' enough_flushs' 
	    valid_program_history' valid' m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' 
	  by (auto simp del: fun_upd_apply )
      qed
    next
      case SBHFence
      then obtain 
	"is\<^sub>s\<^sub>b": "is\<^sub>s\<^sub>b = Fence # is\<^sub>s\<^sub>b'" and
	sb: "sb=[]" and
	\<O>\<^sub>s\<^sub>b': "\<O>\<^sub>s\<^sub>b'=\<O>\<^sub>s\<^sub>b" and
        \<R>\<^sub>s\<^sub>b': "\<R>\<^sub>s\<^sub>b'=Map.empty" and
	\<theta>\<^sub>s\<^sub>b': "\<theta>\<^sub>s\<^sub>b' = \<theta>\<^sub>s\<^sub>b" and
	\<D>\<^sub>s\<^sub>b': "\<not> \<D>\<^sub>s\<^sub>b'" and
	sb': "sb'=sb" and
	m\<^sub>s\<^sub>b': "m\<^sub>s\<^sub>b' = m\<^sub>s\<^sub>b" and
	\<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'=\<S>\<^sub>s\<^sub>b" 
	by auto

      have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof -
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b []"
	    by simp
	  from outstanding_non_volatile_refs_owned_or_read_only_nth_update [OF i_bound this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	qed
      next
	from outstanding_volatile_writes_unowned_by_others_store_buffer 
	[OF i_bound ts\<^sub>s\<^sub>b_i subset_refl]
	show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'" 
	  by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      next
	from read_only_reads_unowned_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i, of "[]" \<O>\<^sub>s\<^sub>b]
	show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      next
	from ownership_distinct_instructions_read_value_store_buffer_independent 
	[OF i_bound ts\<^sub>s\<^sub>b_i]
	show "ownership_distinct ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      qed


      have valid_hist': "valid_history program_step ts\<^sub>s\<^sub>b'"
      proof -
	from valid_history [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b []) []" by simp
	from valid_history_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
      qed
      
      have valid_reads': "valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b'"
      proof -
	have "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b []" by simp
	from valid_reads_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      qed


      have valid_sharing': "valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b []" 
	  by (simp add: sb)
	from outstanding_non_volatile_writes_unshared_nth_update [OF i_bound this]
	show "outstanding_non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' sb sb' \<S>\<^sub>s\<^sub>b')
      next
	have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b []" by simp
	from sharing_consis_nth_update [OF i_bound this]
	show "sharing_consis \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' sb \<S>\<^sub>s\<^sub>b')
      next
	from read_only_unowned_nth_update [OF i_bound read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] ]
	show "read_only_unowned \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b')
      next
	from unowned_shared_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i subset_refl]
	show "unowned_shared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b') 
      next
	from no_outstanding_write_to_read_only_memory_nth_update [OF i_bound, of "[]"]
	show "no_outstanding_write_to_read_only_memory \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' sb)
      qed

      have tmps_distinct': "tmps_distinct ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_load_tmps is\<^sub>s\<^sub>b'" 
	  by (auto simp add: "is\<^sub>s\<^sub>b" split: instr.splits)
	from load_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b")
      next
	from read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_read_tmps []" by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
	from read_tmps_distinct_nth_update [OF i_bound this]
	show "read_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      next
	from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] 
          load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> read_tmps [] = {}"
	  by (clarsimp)
	from load_tmps_read_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_read_tmps_distinct ts\<^sub>s\<^sub>b'"  by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      qed

      have valid_sops': "valid_sops ts\<^sub>s\<^sub>b'"
      proof -
	from valid_store_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	obtain 
	  valid_store_sops': "\<forall>sop\<in>store_sops is\<^sub>s\<^sub>b'. valid_sop sop"
	  by (auto simp add: "is\<^sub>s\<^sub>b" ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')

	from valid_sops_nth_update [OF i_bound  _ valid_store_sops', where sb= "[]" ]
	show ?thesis by (auto simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      qed

      have valid_dd': "valid_data_dependency ts\<^sub>s\<^sub>b'"
      proof -
	from data_dependency_consistent_instrs [OF i_bound ts\<^sub>s\<^sub>b_i]
	obtain 
	  dd_is: "data_dependency_consistent_instrs (dom \<theta>\<^sub>s\<^sub>b') is\<^sub>s\<^sub>b'"
	  by (auto simp add: "is\<^sub>s\<^sub>b" \<theta>\<^sub>s\<^sub>b')
	from load_tmps_write_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> \<Union>(fst ` write_sops [])  = {}"
	  by (auto simp add: write_sops_append)
	from valid_data_dependency_nth_update [OF i_bound dd_is this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      qed

      have load_tmps_fresh': "load_tmps_fresh ts\<^sub>s\<^sub>b'"
      proof -
	from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> dom \<theta>\<^sub>s\<^sub>b = {}"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	from load_tmps_fresh_nth_update [OF i_bound this]
	show ?thesis by (simp add: "is\<^sub>s\<^sub>b" ts\<^sub>s\<^sub>b' sb' sb \<theta>\<^sub>s\<^sub>b')
      qed


      from enough_flushs_nth_update [OF i_bound, where sb="[]" ]
      have enough_flushs': "enough_flushs ts\<^sub>s\<^sub>b'"
	by (auto simp add: ts\<^sub>s\<^sub>b' sb' sb)

      have valid_program_history': "valid_program_history ts\<^sub>s\<^sub>b'"
      proof -	
	have causal': "causal_program_history is\<^sub>s\<^sub>b' sb'"
	  by (simp add: "is\<^sub>s\<^sub>b" sb sb')
	have "last_prog p\<^sub>s\<^sub>b sb' = p\<^sub>s\<^sub>b"
	  by (simp add: sb' sb)
	from valid_program_history_nth_update [OF i_bound causal' this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      from is_sim have "is": "is = Fence # is\<^sub>s\<^sub>b'"
	by (simp add: suspends sb "is\<^sub>s\<^sub>b")
      with ts_i 
      have ts_i: "ts!i = (p\<^sub>s\<^sub>b, Fence # is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b,(), \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b, release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
	by (simp add: suspends sb)

      from direct_memop_step.Fence 
      have "(Fence # is\<^sub>s\<^sub>b',
	    \<theta>\<^sub>s\<^sub>b, (),m,\<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b, release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b, \<S>) \<rightarrow> 
        (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), m, False, acquired True ?take_sb \<O>\<^sub>s\<^sub>b, Map.empty, \<S>)".
      from direct_computation.concurrent_step.Memop [OF i_bound' ts_i this] 
      have "(ts, m, \<S>) \<Rightarrow>\<^sub>d 
        (ts[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), False, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,Map.empty)], m, \<S>)".

      moreover

      have "(ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> (ts[i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b,(), False,acquired True ?take_sb \<O>\<^sub>s\<^sub>b,Map.empty)],m,\<S>)"
	apply (rule sim_config.intros) 
	apply    (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' m 
	  flush_all_until_volatile_nth_update_unused [OF i_bound ts\<^sub>s\<^sub>b_i])
	using   share_all_until_volatile_write_Fence_commute 
	           [OF i_bound ts\<^sub>s\<^sub>b_i [simplified is\<^sub>s\<^sub>b sb]]
	apply  (clarsimp simp add: \<S> ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' is\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb' sb)
	using  leq
	apply  (simp add: ts\<^sub>s\<^sub>b')
	using i_bound i_bound' ts_sim 
	apply (clarsimp simp add: Let_def nth_list_update 
	  ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<D>\<^sub>s\<^sub>b' ex_not  \<theta>\<^sub>s\<^sub>b'
	  split: if_split_asm ) 
	done
      ultimately 
      show ?thesis
	using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' valid_sops'
	  valid_dd' load_tmps_fresh' enough_flushs' 
	  valid_program_history' valid' m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' 
	by (auto simp del: fun_upd_apply)
    next	
      case (SBHRMWReadOnly cond t a D f ret A L R W)
      then obtain 
	"is\<^sub>s\<^sub>b": "is\<^sub>s\<^sub>b = RMW a t (D,f) cond ret A L R W # is\<^sub>s\<^sub>b'" and
	cond: "\<not> (cond (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m\<^sub>s\<^sub>b a)))" and
	\<O>\<^sub>s\<^sub>b': "\<O>\<^sub>s\<^sub>b'=\<O>\<^sub>s\<^sub>b" and
        \<R>\<^sub>s\<^sub>b': "\<R>\<^sub>s\<^sub>b'=Map.empty" and
	\<theta>\<^sub>s\<^sub>b': "\<theta>\<^sub>s\<^sub>b' = \<theta>\<^sub>s\<^sub>b(t\<mapsto>m\<^sub>s\<^sub>b a)" and
	\<D>\<^sub>s\<^sub>b': "\<not> \<D>\<^sub>s\<^sub>b'" and
	sb: "sb=[]" and
	sb': "sb'=[]" and
	m\<^sub>s\<^sub>b': "m\<^sub>s\<^sub>b' = m\<^sub>s\<^sub>b" and
	\<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'=\<S>\<^sub>s\<^sub>b" 
	by auto

      from safe_RMW_common  [OF safe_memop_flush_sb [simplified is\<^sub>s\<^sub>b]]
      obtain access_cond: "a \<in> \<O>\<^sub>s\<^sub>b \<or> a \<in> dom \<S>" and
      rels_cond: " \<forall>j < length ts. i\<noteq>j \<longrightarrow> released (ts!j) a \<noteq> Some False"
        by (auto simp add: \<S> sb)
	

      have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof -
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b []"
	    by simp
	  from outstanding_non_volatile_refs_owned_or_read_only_nth_update [OF i_bound this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	qed
      next
	from outstanding_volatile_writes_unowned_by_others_store_buffer 
	[OF i_bound ts\<^sub>s\<^sub>b_i subset_refl]
	show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'" 
	  by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next
	from read_only_reads_unowned_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i, of "[]" \<O>\<^sub>s\<^sub>b]
	show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      next
	from ownership_distinct_instructions_read_value_store_buffer_independent 
	[OF i_bound ts\<^sub>s\<^sub>b_i]
	show "ownership_distinct ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      qed


      have valid_hist': "valid_history program_step ts\<^sub>s\<^sub>b'"
      proof -
	from valid_history [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "history_consistent (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m\<^sub>s\<^sub>b a)) (hd_prog p\<^sub>s\<^sub>b []) []" by simp
	from valid_history_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
      qed
      
      have valid_reads': "valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b'"
      proof -
	have "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b []" by simp
	from valid_reads_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      qed


      have valid_sharing': "valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	from outstanding_non_volatile_writes_unshared [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b []" 
	  by (simp add: sb)
	from outstanding_non_volatile_writes_unshared_nth_update [OF i_bound this]
	show "outstanding_non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' sb sb' \<S>\<^sub>s\<^sub>b')
      next
	have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b []" by simp
	from sharing_consis_nth_update [OF i_bound this]
	show "sharing_consis \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' sb \<S>\<^sub>s\<^sub>b')
      next
	from read_only_unowned_nth_update [OF i_bound read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] ]
	show "read_only_unowned \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b')
      next
	from unowned_shared_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i subset_refl]
	show "unowned_shared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next 
	from no_outstanding_write_to_read_only_memory_nth_update [OF i_bound, of "[]"]
	show "no_outstanding_write_to_read_only_memory \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' sb)
      qed

      have tmps_distinct': "tmps_distinct ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_load_tmps is\<^sub>s\<^sub>b'" 
	  by (auto simp add: "is\<^sub>s\<^sub>b" split: instr.splits)
	from load_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b")
      next
	from read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_read_tmps []" by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
	from read_tmps_distinct_nth_update [OF i_bound this]
	show "read_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      next
	from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] 
          load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> read_tmps [] = {}"
	  by (clarsimp)
	from load_tmps_read_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_read_tmps_distinct ts\<^sub>s\<^sub>b'"  by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      qed

      have valid_sops': "valid_sops ts\<^sub>s\<^sub>b'"
      proof -
	from valid_store_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	obtain 
	  valid_store_sops': "\<forall>sop\<in>store_sops is\<^sub>s\<^sub>b'. valid_sop sop"
	  by (auto simp add: "is\<^sub>s\<^sub>b" ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')

	from valid_sops_nth_update [OF i_bound  _ valid_store_sops', where sb= "[]" ]
	show ?thesis by (auto simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      qed

      have valid_dd': "valid_data_dependency ts\<^sub>s\<^sub>b'"
      proof -
	from data_dependency_consistent_instrs [OF i_bound ts\<^sub>s\<^sub>b_i]
	obtain 
	  dd_is: "data_dependency_consistent_instrs (dom \<theta>\<^sub>s\<^sub>b') is\<^sub>s\<^sub>b'"
	  by (auto simp add: "is\<^sub>s\<^sub>b" \<theta>\<^sub>s\<^sub>b')
	from load_tmps_write_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> \<Union>(fst ` write_sops [])  = {}"
	  by (auto simp add: write_sops_append)
	from valid_data_dependency_nth_update [OF i_bound dd_is this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      qed


      have load_tmps_fresh': "load_tmps_fresh ts\<^sub>s\<^sub>b'"
      proof -
	from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "load_tmps (RMW a t (D,f) cond ret A L R W# is\<^sub>s\<^sub>b') \<inter> dom \<theta>\<^sub>s\<^sub>b = {}"
	  by (simp add: "is\<^sub>s\<^sub>b")
	moreover
	from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] have "t \<notin> load_tmps is\<^sub>s\<^sub>b'"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	ultimately have "load_tmps is\<^sub>s\<^sub>b' \<inter> dom (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m\<^sub>s\<^sub>b a)) = {}"
	  by auto
	from load_tmps_fresh_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<theta>\<^sub>s\<^sub>b')
      qed

      from enough_flushs_nth_update [OF i_bound, where sb="[]" ]
      have enough_flushs': "enough_flushs ts\<^sub>s\<^sub>b'"
	by (auto simp add: ts\<^sub>s\<^sub>b' sb' sb)

      have valid_program_history': "valid_program_history ts\<^sub>s\<^sub>b'"
      proof -	
	have causal': "causal_program_history is\<^sub>s\<^sub>b' sb'"
	  by (simp add: "is\<^sub>s\<^sub>b" sb sb')
	have "last_prog p\<^sub>s\<^sub>b sb' = p\<^sub>s\<^sub>b"
	  by (simp add: sb' sb)
	from valid_program_history_nth_update [OF i_bound causal' this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      from is_sim have "is": "is = RMW a t (D,f) cond ret A L R W# is\<^sub>s\<^sub>b'"
	by (simp add: suspends sb "is\<^sub>s\<^sub>b")
      with ts_i 
      have ts_i: "ts!i = (p\<^sub>s\<^sub>b, RMW a t (D,f) cond ret A L R W# is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b,(), 
	\<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b, release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
	by (simp add: suspends sb)
      
	
      have "flush_all_until_volatile_write ts\<^sub>s\<^sub>b m\<^sub>s\<^sub>b a = m\<^sub>s\<^sub>b a"
      proof -
        have "\<forall>j < length ts\<^sub>s\<^sub>b. i \<noteq> j \<longrightarrow>
          (let (_,_,_,sb\<^sub>j,_,_,_) = ts\<^sub>s\<^sub>b!j 
          in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))"
	proof -
	  {
	    fix j p\<^sub>j "is\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	    assume neq_i_j: "i \<noteq> j"
	    assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j, xs\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j,\<R>\<^sub>j)"
	    have "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    proof 
	      let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	      let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	      assume a_in: "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b ?take_sb\<^sub>j"
	      with outstanding_refs_takeWhile [where P'= "Not \<circ> is_volatile_Write\<^sub>s\<^sub>b"]
	      have a_in': "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
		by auto
	      with non_volatile_owned_or_read_only_outstanding_non_volatile_writes 
	      [OF outstanding_non_volatile_refs_owned_or_read_only [OF j_bound jth]]
	      have j_owns: "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
		by auto
              from rels_cond [rule_format, OF j_bound [simplified leq] neq_i_j] ts_sim [rule_format, OF j_bound] jth
              have no_unsharing:"release ?take_sb\<^sub>j (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>j  a \<noteq> Some False"
                by (auto simp add: Let_def)
	      from access_cond
	      show False
	      proof 
		assume "a \<in> \<O>\<^sub>s\<^sub>b"
		with ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth] 
		  j_owns 
		show False
		  by auto
	      next
		assume a_shared: "a \<in> dom \<S>"
                with share_all_until_volatile_write_thread_local [OF ownership_distinct_ts\<^sub>s\<^sub>b sharing_consis_ts\<^sub>s\<^sub>b j_bound jth j_owns]
                have a_dom: "a \<in> dom  (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
                  by (auto simp add: \<S> domIff)
		from outstanding_non_volatile_writes_unshared [OF j_bound jth]
		have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b sb\<^sub>j".
		with non_volatile_writes_unshared_append [of \<S>\<^sub>s\<^sub>b "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
		  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
		have unshared_take: "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		  by clarsimp

                from release_not_unshared_no_write_take [OF  unshared_take no_unsharing a_dom] a_in
                show False by auto
	      qed
	    qed
	  } 
	  thus ?thesis
	    by (fastforce simp add: Let_def)
	qed

	from flush_all_until_volatile_write_buffered_val_conv 
	[OF _ i_bound ts\<^sub>s\<^sub>b_i this]
	show ?thesis
	  by (simp add: sb)
      qed
      
      hence m_a: "m a = m\<^sub>s\<^sub>b a"
	by (simp add: m)

      from cond have cond': "\<not> cond (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a))"
	by (simp add: m_a)

      from direct_memop_step.RMWReadOnly [where cond=cond and \<theta>=\<theta>\<^sub>s\<^sub>b and m=m, OF cond']
      have "(RMW a t (D, f) cond ret A L R W # is\<^sub>s\<^sub>b',
             \<theta>\<^sub>s\<^sub>b, (),m, \<D>, \<O>\<^sub>s\<^sub>b, \<R>\<^sub>s\<^sub>b, \<S>) \<rightarrow> 
            (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t \<mapsto> m a), (), m, False, \<O>\<^sub>s\<^sub>b, Map.empty, \<S>)".

      from direct_computation.concurrent_step.Memop [OF i_bound' ts_i [simplified sb, simplified] this]
      have "(ts, m, \<S>) \<Rightarrow>\<^sub>d (ts[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b',
	       \<theta>\<^sub>s\<^sub>b(t \<mapsto> m a), (), False, \<O>\<^sub>s\<^sub>b,Map.empty)], m, \<S>)".

      moreover
      
      have tmps_commute: "\<theta>\<^sub>s\<^sub>b(t \<mapsto> (m\<^sub>s\<^sub>b a)) = 
	(\<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b - {t}))(t \<mapsto> (m\<^sub>s\<^sub>b a))"
	apply (rule ext)
	apply (auto simp add: restrict_map_def domIff)
	done

      have "(ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> (ts[i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t \<mapsto> m a),(), False,\<O>\<^sub>s\<^sub>b,Map.empty)],m,\<S>)"
	apply (rule sim_config.intros)
	apply    (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' m 
	  flush_all_until_volatile_nth_update_unused [OF i_bound ts\<^sub>s\<^sub>b_i, simplified sb])
	using  share_all_until_volatile_write_RMW_commute [OF i_bound ts\<^sub>s\<^sub>b_i [simplified is\<^sub>s\<^sub>b sb]]
	apply  (clarsimp simp add: \<S> ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' is\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb' sb)
	using  leq
	apply  (simp add: ts\<^sub>s\<^sub>b')
	using i_bound i_bound' ts_sim
	apply (clarsimp simp add: Let_def nth_list_update 
	  ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' \<D>\<^sub>s\<^sub>b' ex_not m_a
	  split: if_split_asm)
	apply (rule tmps_commute)
	done
      ultimately 
      show ?thesis
	using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' valid_sops'
	  valid_dd' load_tmps_fresh' enough_flushs' 
	  valid_program_history' valid' m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' 
	by (auto simp del: fun_upd_apply)
    next
      case (SBHRMWWrite cond t a D f ret A L R W) 
      then obtain 
	"is\<^sub>s\<^sub>b": "is\<^sub>s\<^sub>b = RMW a t (D,f) cond ret A L R W # is\<^sub>s\<^sub>b'" and
	cond: "(cond (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m\<^sub>s\<^sub>b a)))" and
	\<O>\<^sub>s\<^sub>b': "\<O>\<^sub>s\<^sub>b'=\<O>\<^sub>s\<^sub>b \<union> A - R" and
        \<R>\<^sub>s\<^sub>b': "\<R>\<^sub>s\<^sub>b'=Map.empty" and
	\<D>\<^sub>s\<^sub>b': "\<not> \<D>\<^sub>s\<^sub>b'" and
	\<theta>\<^sub>s\<^sub>b': "\<theta>\<^sub>s\<^sub>b' = \<theta>\<^sub>s\<^sub>b(t\<mapsto>ret (m\<^sub>s\<^sub>b a) (f (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m\<^sub>s\<^sub>b a))))" and
	sb: "sb=[]" and
	sb': "sb'=[]" and
	m\<^sub>s\<^sub>b': "m\<^sub>s\<^sub>b' = m\<^sub>s\<^sub>b(a := f (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m\<^sub>s\<^sub>b a)))" and
	\<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'=\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" 
	by auto

      from data_dependency_consistent_instrs [OF i_bound ts\<^sub>s\<^sub>b_i]
      have D_subset: "D \<subseteq> dom \<theta>\<^sub>s\<^sub>b" 
	by (simp add: is\<^sub>s\<^sub>b)

      from is_sim have "is": "is = RMW a t (D,f) cond ret A L R W # is\<^sub>s\<^sub>b'"
	by (simp add: suspends sb "is\<^sub>s\<^sub>b")
      with ts_i 
      have ts_i: "ts!i = (p\<^sub>s\<^sub>b, RMW a t (D,f) cond ret A L R W # is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b,(), \<D>, \<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b)"
	by (simp add: suspends sb)
      
      from safe_RMW_common  [OF safe_memop_flush_sb [simplified is\<^sub>s\<^sub>b]]
      obtain access_cond: "a \<in> \<O>\<^sub>s\<^sub>b \<or> a \<in> dom \<S>" and
      rels_cond: " \<forall>j < length ts. i\<noteq>j \<longrightarrow> released (ts!j) a \<noteq> Some False"
        by (auto simp add: \<S> sb)



      have a_unflushed: 
	"\<forall>j < length ts\<^sub>s\<^sub>b. i \<noteq> j \<longrightarrow>
                  (let (_,_,_,sb\<^sub>j,_,_,_) = ts\<^sub>s\<^sub>b!j 
                  in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))"
      proof -
	{
	  fix j p\<^sub>j "is\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	  assume neq_i_j: "i \<noteq> j"
	  assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j, xs\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j, \<R>\<^sub>j)"
	  have "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	  proof 
	    let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    assume a_in: "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b ?take_sb\<^sub>j"
	    with outstanding_refs_takeWhile [where P'= "Not \<circ> is_volatile_Write\<^sub>s\<^sub>b"]
	    have a_in': "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
	      by auto
	    with non_volatile_owned_or_read_only_outstanding_non_volatile_writes 
	    [OF outstanding_non_volatile_refs_owned_or_read_only [OF j_bound jth]]
	    have j_owns: "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	      by auto
	    with ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
	    have a_not_owns: "a \<notin> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
	      by blast
	    assume a_in: "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b 
		(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    with outstanding_refs_takeWhile [where P'= "Not \<circ> is_volatile_Write\<^sub>s\<^sub>b"]
	    have a_in': "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
	      by auto
            from rels_cond [rule_format, OF j_bound [simplified leq] neq_i_j] ts_sim [rule_format, OF j_bound] jth
            have no_unsharing:"release ?take_sb\<^sub>j (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>j  a \<noteq> Some False"
              by (auto simp add: Let_def)
	    from access_cond
	    show False
	    proof 
	      assume "a \<in> \<O>\<^sub>s\<^sub>b"
	      with ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth] 
		j_owns 
	      show False
		by auto
	    next
	      assume a_shared: "a \<in> dom \<S>"
              with share_all_until_volatile_write_thread_local [OF ownership_distinct_ts\<^sub>s\<^sub>b sharing_consis_ts\<^sub>s\<^sub>b j_bound jth j_owns]
              have a_dom: "a \<in> dom  (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
                by (auto simp add: \<S> domIff)
	      from outstanding_non_volatile_writes_unshared [OF j_bound jth]
	      have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b sb\<^sub>j".
	      with non_volatile_writes_unshared_append [of \<S>\<^sub>s\<^sub>b "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
		"(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
	      have unshared_take: "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
	        by clarsimp
              
              from release_not_unshared_no_write_take [OF  unshared_take no_unsharing a_dom] a_in
              show False by auto
	    qed
	  qed
	} 
	thus ?thesis
	  by (fastforce simp add: Let_def)
      qed

      have "flush_all_until_volatile_write ts\<^sub>s\<^sub>b m\<^sub>s\<^sub>b a = m\<^sub>s\<^sub>b a"
      proof -
	from flush_all_until_volatile_write_buffered_val_conv 
	[OF _ i_bound ts\<^sub>s\<^sub>b_i a_unflushed]
	show ?thesis
	  by (simp add: sb)
      qed     
      
      hence m_a: "m a = m\<^sub>s\<^sub>b a"
	by (simp add: m)

      from cond have cond': "cond (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a))"
	by (simp add: m_a)


      from safe_memop_flush_sb [simplified is\<^sub>s\<^sub>b] cond'
      obtain 
	L_subset: "L \<subseteq> A" and
	A_shared_owned: "A \<subseteq> dom \<S> \<union> \<O>\<^sub>s\<^sub>b" and
	R_owned: "R \<subseteq> \<O>\<^sub>s\<^sub>b" and
        A_R: "A \<inter> R = {}" and
	a_unowned_others_ts:
	  "\<forall>j<length ts. i \<noteq> j \<longrightarrow> (a \<notin> owned (ts!j) \<union> dom (released (ts!j)))" and
	A_unowned_by_others_ts:
	  "\<forall>j<length ts. i \<noteq> j \<longrightarrow> (A \<inter> (owned (ts!j) \<union> dom (released (ts!j))) = {})" and
	a_not_ro: "a \<notin> read_only \<S>"
	by cases (auto simp add: sb)

      from a_unowned_others_ts ts_sim leq
      have a_unowned_others:
        "\<forall>j<length ts\<^sub>s\<^sub>b. i \<noteq> j \<longrightarrow> 
          (let (_,_,_,sb\<^sub>j,_,\<O>\<^sub>j,_) = ts\<^sub>s\<^sub>b!j in 
	    a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j \<and>
            a \<notin> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))" 
  apply (clarsimp simp add: Let_def)
  subgoal for j
	apply (drule_tac x=j in spec)
	apply (auto simp add: dom_release_takeWhile)
	done
  done

      from A_unowned_by_others_ts ts_sim leq
      have A_unowned_by_others:  
	"\<forall>j<length ts\<^sub>s\<^sub>b. i\<noteq>j \<longrightarrow> (let (_,_,_,sb\<^sub>j,_,\<O>\<^sub>j,_) = ts\<^sub>s\<^sub>b!j 
	  in A \<inter> (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j \<union>
                  all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)) = {})" 
  apply (clarsimp simp add: Let_def)
  subgoal for j
	apply (drule_tac x=j in spec)
	apply (force simp add: dom_release_takeWhile)
	done
  done

      have a_not_ro': "a \<notin> read_only \<S>\<^sub>s\<^sub>b"
      proof 
	assume a: "a \<in> read_only (\<S>\<^sub>s\<^sub>b)"
	  from local.read_only_unowned_axioms have "read_only_unowned \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b". 
        from in_read_only_share_all_until_volatile_write' [OF ownership_distinct_ts\<^sub>s\<^sub>b sharing_consis_ts\<^sub>s\<^sub>b
          \<open>read_only_unowned \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> i_bound ts\<^sub>s\<^sub>b_i a_unowned_others, simplified sb, simplified, 
          OF a] 
	have "a \<in> read_only (\<S>)"
	  by (simp add: \<S>)
	with a_not_ro show False by simp
      qed

      
      {
	fix j 
	fix p\<^sub>j is\<^sub>s\<^sub>b\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>s\<^sub>b\<^sub>j \<theta>\<^sub>j sb\<^sub>j
	assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	assume ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b!j=(p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	assume neq_i_j: "i\<noteq>j"
	have "a \<notin> unforwarded_non_volatile_reads (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) {}"
	proof 
	  let ?take_sb\<^sub>j = "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j"
	  let ?drop_sb\<^sub>j = "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j"
	  assume a_in: "a \<in>  unforwarded_non_volatile_reads ?drop_sb\<^sub>j {}"

	  from a_unowned_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
	  obtain a_unacq_take: "a \<notin> acquired True ?take_sb\<^sub>j \<O>\<^sub>j" and a_not_shared: "a \<notin> all_shared ?take_sb\<^sub>j"
	    by auto
(*
	  then obtain
	    a_unowned: "a \<notin> \<O>\<^sub>j" and a_unacq_take': "a \<notin> all_acquired ?take_sb\<^sub>j"
	    by (auto simp add: acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)
*)
	  note nvo_j = outstanding_non_volatile_refs_owned_or_read_only [OF j_bound ts\<^sub>s\<^sub>b_j]
	  
	  from non_volatile_owned_or_read_only_drop [OF nvo_j]
	  have nvo_drop_j: "non_volatile_owned_or_read_only True (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)
	                    (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j" .

	  note consis_j = sharing_consis [OF j_bound ts\<^sub>s\<^sub>b_j]
	  with sharing_consistent_append [of \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	  obtain consis_take_j: "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j" and
	    consis_drop_j: "sharing_consistent (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)
	      (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
	    by auto

	  from in_unforwarded_non_volatile_reads_non_volatile_Read\<^sub>s\<^sub>b [OF a_in]
	  have a_in': "a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?drop_sb\<^sub>j".

	  note reads_consis_j = valid_reads [OF j_bound ts\<^sub>s\<^sub>b_j]
	  from reads_consistent_drop [OF this]
	  have reads_consis_drop_j:
	    "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) (flush ?take_sb\<^sub>j m\<^sub>s\<^sub>b) ?drop_sb\<^sub>j".

        
          from read_only_share_all_shared [of a ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b] a_not_ro' a_not_shared
          have a_not_ro_j: "a \<notin> read_only (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
            by auto
          



	  from ts_sim [rule_format, OF j_bound] ts\<^sub>s\<^sub>b_j j_bound
	  obtain suspends\<^sub>j "is\<^sub>j" \<D>\<^sub>j where
	    suspends\<^sub>j: "suspends\<^sub>j = ?drop_sb\<^sub>j" and
	    is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
	    \<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
	    ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j, 
	    \<theta>\<^sub>j |` (dom \<theta>\<^sub>j - read_tmps suspends\<^sub>j),(),   
	    \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	    by (auto simp: Let_def)

	  from ts\<^sub>j neq_i_j j_bound 
	  have ts'_j: "?ts'!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
	    \<theta>\<^sub>j |` (dom \<theta>\<^sub>j - read_tmps suspends\<^sub>j),(), 
	    \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	    by auto

	  from valid_last_prog [OF j_bound ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".

	  from j_bound i_bound' leq have j_bound_ts': "j < length ?ts'"
	    by simp

	  from read_only_read_acquired_unforwarded_acquire_witness [OF nvo_drop_j consis_drop_j
	  a_not_ro_j a_unacq_take a_in]
	  have False
	  proof
	    assume "\<exists>sop a' v ys zs A L R W. 
		?drop_sb\<^sub>j= ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W # zs \<and> a \<in> A \<and> 
                a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys \<and> a'\<noteq>a"
	    with suspends\<^sub>j
	    obtain a' sop' v' ys zs' A' L' R' W' where
		split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# zs'" (is "suspends\<^sub>j=?suspends") and
		a_A': "a \<in> A'" and
		no_write: "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (ys @ [Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'])"
	        by(auto simp add: outstanding_refs_append )
		
	    from last_prog
	    have lp: "last_prog p\<^sub>j suspends\<^sub>j = p\<^sub>j"
	      apply -
	      apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done
	    
	    from sharing_consis [OF j_bound ts\<^sub>s\<^sub>b_j]
	    have sharing_consis_j: "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	    then have A'_R': "A' \<inter> R' = {}" 
	      by (simp add: sharing_consistent_append [of _ _ ?take_sb\<^sub>j ?drop_sb\<^sub>j, simplified] 
		  suspends\<^sub>j [symmetric] split_suspends\<^sub>j sharing_consistent_append)	  

	    from valid_program_history [OF j_bound ts\<^sub>s\<^sub>b_j] 
	    have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	    then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
	      apply -
	      apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply (simp add: split_suspends\<^sub>j)
	      done
	    
	    from valid_reads [OF j_bound ts\<^sub>s\<^sub>b_j]
	    have reads_consis_j: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	    
	   from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> 
	      j_bound ts\<^sub>s\<^sub>b_j this]
	   have reads_consis_m_j: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
	    by (simp add: m suspends\<^sub>j)
	    
	   from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j]
	   have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
	     by (simp add: suspends\<^sub>j)
	   from reads_consistent_flush_independent [OF this reads_consis_m_j]
	   have reads_consis_flush_suspend: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
	        (flush ?drop_sb m) suspends\<^sub>j".

	   hence reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)  
	        (flush ?drop_sb m) (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'])"
	     by (simp add: split_suspends\<^sub>j reads_consistent_append)

  	   from valid_write_sops [OF j_bound ts\<^sub>s\<^sub>b_j]
	   have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
	     by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	   then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		valid_sops_drop: "\<forall>sop\<in>write_sops (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']). valid_sop sop"
	     apply (simp only: write_sops_append)
	     apply auto
	     done
	    
	   from read_tmps_distinct [OF j_bound ts\<^sub>s\<^sub>b_j]
	   have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
	     by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	   then obtain 
	     read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
	     distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
	     apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	     apply (simp only: distinct_read_tmps_append)
	     done
	    
	   from valid_history [OF j_bound ts\<^sub>s\<^sub>b_j]
	   have h_consis: 
	      "history_consistent \<theta>\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done
	    
	   have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	   proof -
	     from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
	       by simp
	     from last_prog_hd_prog_append' [OF h_consis] this
	     have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
	       by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	     moreover 
	     have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
	       last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
	       apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	       by (rule last_prog_hd_prog_append)
	     ultimately show ?thesis
	       by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	   qed

	   from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
	      h_consis] last_prog_hd_prog
	   have hist_consis': "history_consistent \<theta>\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
	     by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	   from reads_consistent_drop_volatile_writes_no_volatile_reads  
	   [OF reads_consis_j] 
	   have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b 
	      (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) = {}"
	     by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		split_suspends\<^sub>j )
	    
	   have acq_simp:
	      "acquired True (ys @ [Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) 
              (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) = 
              acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R'"
	     by (simp add: acquired_append)

	   from flush_store_buffer_append [where sb="ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']" and sb'="zs'", simplified,
	      OF j_bound_ts' is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
	      ts'_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_ys 
	      hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
	      distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
	      no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
	      \<S>="share ?drop_sb \<S>"]
	    
	   obtain is\<^sub>j' \<R>\<^sub>j' where
	      is\<^sub>j': "instrs zs' @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs'" and
	      steps_ys: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>)  \<Rightarrow>\<^sub>d\<^sup>* 
		  (?ts'[j:=(last_prog
                              (hd_prog p\<^sub>j (Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# zs')) (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']),
                             is\<^sub>j',
                             \<theta>\<^sub>j |` (dom \<theta>\<^sub>j - read_tmps zs'),
                              (), True, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R',\<R>\<^sub>j')],
                    flush (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) (flush ?drop_sb m),
                    share (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) (share ?drop_sb \<S>))"
		   (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
             by (auto simp add: acquired_append outstanding_refs_append)

	   from i_bound' have i_bound_ys: "i < length ?ts_ys"
	     by auto
	    
	   from i_bound' neq_i_j 
	   have ts_ys_i: "?ts_ys!i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b,(), 
	      \<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b, release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
	     by simp
	   note conflict_computation = rtranclp_trans [OF steps_flush_sb steps_ys]
	    
	   from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	   have safe: "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	      
	   from flush_unchanged_addresses [OF no_write] 
	   have "flush (ys @ [Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) m a = m a".
	    
	   with safe_delayedE [OF safe i_bound_ys ts_ys_i, simplified is\<^sub>s\<^sub>b] cond'
	   have a_unowned: 
	      
	      "\<forall>j < length ?ts_ys. i\<noteq>j \<longrightarrow> (let (\<O>\<^sub>j) = map owned ?ts_ys!j in a \<notin> \<O>\<^sub>j)"
	     apply cases
	     apply (auto simp add: Let_def is\<^sub>s\<^sub>b sb)
	     done
	   from a_A' a_unowned [rule_format, of j] neq_i_j j_bound leq A'_R'
	    show False
	      by (auto simp add: Let_def)
	  next
	    assume "\<exists>A L R W ys zs. ?drop_sb\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys"
	    with  suspends\<^sub>j 
	    obtain ys zs' A' L' R' W' where
	      split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs'" (is "suspends\<^sub>j=?suspends") and
	      a_A': "a \<in> A'" and
	      no_write: "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W'])"
	      by (auto simp add: outstanding_refs_append)

	    from last_prog
	    have lp: "last_prog p\<^sub>j suspends\<^sub>j = p\<^sub>j"
	      apply -
	      apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done
	    from sharing_consis [OF j_bound ts\<^sub>s\<^sub>b_j]
	    have sharing_consis_j: "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	    then have A'_R': "A' \<inter> R' = {}" 
	      by (simp add: sharing_consistent_append [of _ _ ?take_sb\<^sub>j ?drop_sb\<^sub>j, simplified] 
		  suspends\<^sub>j [symmetric] split_suspends\<^sub>j sharing_consistent_append)	  


	    from valid_program_history [OF j_bound ts\<^sub>s\<^sub>b_j] 
	    have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	    then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
	      apply -
	      apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply (simp add: split_suspends\<^sub>j)
	      done
	    
	    from valid_reads [OF j_bound ts\<^sub>s\<^sub>b_j]
	    have reads_consis_j: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	    
	    from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> 
	      j_bound ts\<^sub>s\<^sub>b_j this]
	    have reads_consis_m_j: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
	      by (simp add: m suspends\<^sub>j)
	    
	    from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j]
	    have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
	      by (simp add: suspends\<^sub>j)
	    from reads_consistent_flush_independent [OF this reads_consis_m_j]
	    have reads_consis_flush_suspend: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
	      (flush ?drop_sb m) suspends\<^sub>j".

	    hence reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)  
	      (flush ?drop_sb m) (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W'])"
	      by (simp add: split_suspends\<^sub>j reads_consistent_append)

	    from valid_write_sops [OF j_bound ts\<^sub>s\<^sub>b_j]
	    have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
	      valid_sops_drop: "\<forall>sop\<in>write_sops (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']). valid_sop sop"
	      apply (simp only: write_sops_append)
	      apply auto
	      done
	    
	    from read_tmps_distinct [OF j_bound ts\<^sub>s\<^sub>b_j]
	    have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    then obtain 
	      read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
	      distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      apply (simp only: distinct_read_tmps_append)
	      done
	    
	    from valid_history [OF j_bound ts\<^sub>s\<^sub>b_j]
	    have h_consis: 
	      "history_consistent \<theta>\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done
	    
	    have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	    proof -
	      from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		by simp
	      from last_prog_hd_prog_append' [OF h_consis] this
	      have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      moreover 
	      have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		by (rule last_prog_hd_prog_append)
	      ultimately show ?thesis
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	    qed

	    from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
	      h_consis] last_prog_hd_prog
	    have hist_consis': "history_consistent \<theta>\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    from reads_consistent_drop_volatile_writes_no_volatile_reads  
	    [OF reads_consis_j] 
	    have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b 
	      (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) = {}"
	      by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		split_suspends\<^sub>j )
	    
	    have acq_simp:
	      "acquired True (ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W']) 
              (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) = 
              acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R'"
	      by (simp add: acquired_append)

	    from flush_store_buffer_append [where sb="ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']" and sb'="zs'", simplified,
	      OF j_bound_ts' is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
	      ts'_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_ys 
	      hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
	      distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
	      no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
	      \<S>="share ?drop_sb \<S>"]
	    
	    obtain is\<^sub>j' \<R>\<^sub>j' where
	      is\<^sub>j': "instrs zs' @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs'" and
	      steps_ys: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>)  \<Rightarrow>\<^sub>d\<^sup>* 
		  (?ts'[j:=(last_prog
                              (hd_prog p\<^sub>j (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs')) (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']),
                             is\<^sub>j',
                             \<theta>\<^sub>j |` (dom \<theta>\<^sub>j - read_tmps zs'),
                              (), 
	                     \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R',\<R>\<^sub>j')],
                    flush (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) (flush ?drop_sb m),
                    share (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) (share ?drop_sb \<S>))"
		   (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
              by (auto simp add: acquired_append outstanding_refs_append)

	    from i_bound' have i_bound_ys: "i < length ?ts_ys"
	      by auto
	    
	    from i_bound' neq_i_j 
	    have ts_ys_i: "?ts_ys!i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b,(), 
	      \<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b, release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
	      by simp
	    note conflict_computation = rtranclp_trans [OF steps_flush_sb steps_ys]
	    
	    from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	    have safe: "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	      
	    from flush_unchanged_addresses [OF no_write] 
	    have "flush (ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W']) m a = m a".
	    
	    with safe_delayedE [OF safe i_bound_ys ts_ys_i, simplified is\<^sub>s\<^sub>b] cond'
	    have a_unowned: 
	      
	      "\<forall>j < length ?ts_ys. i\<noteq>j \<longrightarrow> (let (\<O>\<^sub>j) = map owned ?ts_ys!j in a \<notin> \<O>\<^sub>j)"
	      apply cases
	      apply (auto simp add: Let_def is\<^sub>s\<^sub>b sb)
	      done
	    from a_A' a_unowned [rule_format, of j] neq_i_j j_bound leq A'_R'

	    show False
	      by (auto simp add: Let_def)
	  qed
	  then show False
	    by simp
	qed
      }
      note a_notin_unforwarded_non_volatile_reads_drop = this

      (* FIXME: split in to theorems, one for A \<inter> \<O>\<^sub>j and  one for
	 A \<inter> outstanding_refs\<dots>    *) 
      have A_unused_by_others:
	  "\<forall>j<length (map \<O>_sb ts\<^sub>s\<^sub>b). i \<noteq> j \<longrightarrow>
             (let (\<O>\<^sub>j, sb\<^sub>j) = map \<O>_sb ts\<^sub>s\<^sub>b! j
             in A  \<inter> (\<O>\<^sub>j \<union> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j) = {})"
      proof -
	{
	  fix j \<O>\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length (map owned ts\<^sub>s\<^sub>b)"
	  assume neq_i_j: "i\<noteq>j"
	  assume ts\<^sub>s\<^sub>b_j: "(map \<O>_sb ts\<^sub>s\<^sub>b)!j = (\<O>\<^sub>j,sb\<^sub>j)"
	  assume conflict: "A \<inter> (\<O>\<^sub>j \<union> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j) \<noteq> {}"
	  have False
	  proof -
	    from j_bound leq
	    have j_bound': "j < length (map owned ts)"
	      by auto
	    from j_bound have j_bound'': "j < length ts\<^sub>s\<^sub>b"
	      by auto
	    from j_bound' have j_bound''': "j < length ts"
	      by simp
	    
	    from conflict obtain a' where
	      a_in: "a' \<in> A" and
              conflict: "a' \<in> \<O>\<^sub>j \<or> a' \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
	      by auto
            from A_unowned_by_others [rule_format, OF _ neq_i_j] j_bound  ts\<^sub>s\<^sub>b_j
            have A_unshared_j: "A \<inter> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) = {}"
              by (auto simp add: Let_def)
	    from conflict
	    show ?thesis
	    proof

 	      assume "a' \<in> \<O>\<^sub>j"

              from all_shared_acquired_in [OF this] A_unshared_j a_in
	      have conflict: "a' \<in> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j"
	        by (auto)
              with A_unowned_by_others [rule_format, OF _ neq_i_j] j_bound  ts\<^sub>s\<^sub>b_j a_in
              show False by auto
	    next
	      assume a_in_j: "a' \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"

	      let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	      let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"

	      from ts_sim [rule_format, OF  j_bound''] ts\<^sub>s\<^sub>b_j j_bound''
	      obtain p\<^sub>j suspends\<^sub>j "is\<^sub>s\<^sub>b\<^sub>j" \<D>\<^sub>s\<^sub>b\<^sub>j \<D>\<^sub>j \<R>\<^sub>j \<theta>\<^sub>s\<^sub>b\<^sub>j "is\<^sub>j" where
		  ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j, \<theta>\<^sub>s\<^sub>b\<^sub>j, sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
		  suspends\<^sub>j: "suspends\<^sub>j = ?drop_sb\<^sub>j" and
		  \<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
		  is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
		  ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
		       \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
		apply (cases "ts\<^sub>s\<^sub>b!j")
		apply (force simp add: Let_def)
		done
	      


	      have "a' \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b suspends\<^sub>j"
	      proof -	
		from a_in_j 
		have "a' \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (?take_sb\<^sub>j @ ?drop_sb\<^sub>j)"
		  by simp
		thus ?thesis
		  apply (simp only: outstanding_refs_append suspends\<^sub>j)
		  apply (auto simp add: outstanding_refs_conv dest: set_takeWhileD)
		  done
	      qed
		 
	      from split_volatile_Write\<^sub>s\<^sub>b_in_outstanding_refs [OF this]
	      obtain sop' v' ys zs A' L' R' W' where
		split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# zs" (is "suspends\<^sub>j = ?suspends")
		by blast
	      


	      from valid_program_history [OF j_bound'' ts\<^sub>s\<^sub>b_j] 
	      have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	      then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
		apply -
		apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply (simp add: split_suspends\<^sub>j)
		done

	      from valid_last_prog [OF j_bound'' ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	      then
	      have lp: "last_prog p\<^sub>j ?suspends = p\<^sub>j"
		apply -
		apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply simp
		done

	      from valid_reads [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have reads_consis: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	      from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> 
		j_bound''
		ts\<^sub>s\<^sub>b_j this]
	      have reads_consis_m_j: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
		by (simp add: m suspends\<^sub>j)

	      from outstanding_non_volatile_refs_owned_or_read_only [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have nvo_j: "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	      with non_volatile_owned_or_read_only_append [of False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	      have nvo_take_j: "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j"
		by auto

	      from a_unowned_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
	      have a_not_acq: "a \<notin> acquired True ?take_sb\<^sub>j \<O>\<^sub>j"
		by auto

	      from a_notin_unforwarded_non_volatile_reads_drop[OF j_bound'' ts\<^sub>s\<^sub>b_j neq_i_j]
	      have a_notin_unforwarded_reads: "a \<notin> unforwarded_non_volatile_reads suspends\<^sub>j {}"
		by (simp add: suspends\<^sub>j)
		
	      let ?ma="(m(a := f (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m a))))"

	      from reads_consistent_mem_eq_on_unforwarded_non_volatile_reads [where W="{}" 
		and m'="?ma",simplified, OF _ subset_refl reads_consis_m_j] 
		a_notin_unforwarded_reads
	      have reads_consis_ma_j: 
		"reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?ma suspends\<^sub>j"
		by auto

	      from reads_consis_ma_j 
	      have reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?ma (ys)"
		by (simp add: split_suspends\<^sub>j reads_consistent_append)

	      from direct_memop_step.RMWWrite [where cond=cond and \<theta>=\<theta>\<^sub>s\<^sub>b and m=m, OF cond' ]
	      have "(RMW a t (D, f) cond ret A L R W# is\<^sub>s\<^sub>b',  \<theta>\<^sub>s\<^sub>b, (), m,\<D>, \<O>\<^sub>s\<^sub>b, \<R>\<^sub>s\<^sub>b, \<S>) \<rightarrow> 
                    (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a)))), (), ?ma, False, \<O>\<^sub>s\<^sub>b \<union> A - R, Map.empty,\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".
	      from direct_computation.concurrent_step.Memop [OF i_bound' ts_i  this] 
	      have step_a: "(ts, m, \<S>) \<Rightarrow>\<^sub>d 
                    (ts[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a)))), (), False, \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)], 
                      ?ma,\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		(is " _ \<Rightarrow>\<^sub>d (?ts_a, _, ?shared_a)").

	      from ts\<^sub>j neq_i_j j_bound 

	      have ts_a_j: "?ts_a!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
		\<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom (\<S>\<^sub>s\<^sub>b)) \<R>\<^sub>j)"
		by auto


	      from valid_write_sops [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		valid_sops_drop: "\<forall>sop\<in>write_sops (ys). valid_sop sop"
		apply (simp only: write_sops_append)
		apply auto
		done

	      from read_tmps_distinct [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      then obtain 
		read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
	      distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		apply (simp only: distinct_read_tmps_append)
		done
	    
	      from valid_history [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	      have h_consis: 
		"history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply simp
		done
	    
	      have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	      proof -
		from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		  by simp
	      from last_prog_hd_prog_append' [OF h_consis] this
	      have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      moreover 
	      have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		by (rule last_prog_hd_prog_append)
	      ultimately show ?thesis
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	    qed

	    from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
	      h_consis] last_prog_hd_prog
	    have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    from reads_consistent_drop_volatile_writes_no_volatile_reads  
	    [OF reads_consis] 
	    have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b (ys) = {}"
	      by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		split_suspends\<^sub>j )
	    from j_bound' have j_bound_ts_a: "j < length ?ts_a" by auto

	    
	    from flush_store_buffer_append [where sb="ys" and sb'="Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'#zs", simplified,
	    OF j_bound_ts_a is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
ts_a_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_ys
 	      hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
	      distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
              no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
	      \<S>="?shared_a"]

	    obtain is\<^sub>j' \<R>\<^sub>j' where
	      is\<^sub>j': "Write True a' sop' A' L' R' W'# instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs" and
	      steps_ys: "(?ts_a, ?ma, ?shared_a)  \<Rightarrow>\<^sub>d\<^sup>* 
		(?ts_a[j:=(last_prog
                            (hd_prog p\<^sub>j zs) ys,
              is\<^sub>j',
                           \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps zs),
                            (), \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')],
                  flush ys (?ma),    share ys (?shared_a))"
		 (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
              by (auto simp add: acquired_append)

	    from cph
	    have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ((ys @ [Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) @ zs)"
	      by simp
	    from causal_program_history_suffix [OF this]
	    have cph': "causal_program_history is\<^sub>s\<^sub>b\<^sub>j zs".	      
	    interpret causal\<^sub>j: causal_program_history "is\<^sub>s\<^sub>b\<^sub>j" "zs" by (rule cph')

	    from causal\<^sub>j.causal_program_history [of "[]", simplified, OF refl] is\<^sub>j'   
	    obtain is\<^sub>j''
	      where is\<^sub>j': "is\<^sub>j' = Write True a' sop' A' L' R' W'#is\<^sub>j''" and
	      is\<^sub>j'': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j'' @ prog_instrs zs"
	      by clarsimp
	    
	    from i_bound' have i_bound_ys: "i < length ?ts_ys"
	      by auto

	    from i_bound' neq_i_j 
	    have ts_ys_i: "?ts_ys!i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', 
	      \<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a)))),(), False, \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)"
	      by simp

	    from j_bound_ts_a have j_bound_ys: "j < length ?ts_ys"
	      by auto
	    then have ts_ys_j: "?ts_ys!j = (last_prog (hd_prog p\<^sub>j zs) ys, Write True a' sop' A' L' R' W'#is\<^sub>j'', \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps zs), (), \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, 
	      acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')"
	      by (clarsimp simp add: is\<^sub>j')
	    note conflict_computation = r_rtranclp_rtranclp [OF step_a steps_ys]
	    
	    from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	    have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".


	      from safe_delayedE [OF this j_bound_ys ts_ys_j]
	      have a_unowned: 
		"\<forall>i < length ts. j\<noteq>i \<longrightarrow> (let (\<O>\<^sub>i) = map owned ?ts_ys!i in a' \<notin> \<O>\<^sub>i)"
		apply cases
		apply (auto simp add: Let_def)
		done
	      from a_in a_unowned [rule_format, of i] neq_i_j i_bound' A_R 
	      show False
		by (auto simp add: Let_def)
	    qed
	  qed
	}
	thus ?thesis
	  by (auto simp add: Let_def)
      qed

      have A_unacquired_by_others:
	  "\<forall>j<length (map \<O>_sb ts\<^sub>s\<^sub>b). i \<noteq> j \<longrightarrow>
             (let (\<O>\<^sub>j, sb\<^sub>j) = map \<O>_sb ts\<^sub>s\<^sub>b! j
             in A \<inter> all_acquired sb\<^sub>j = {})"
      proof -
	{
	  fix j \<O>\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length (map owned ts\<^sub>s\<^sub>b)"
	  assume neq_i_j: "i\<noteq>j"
	  assume ts\<^sub>s\<^sub>b_j: "(map \<O>_sb ts\<^sub>s\<^sub>b)!j = (\<O>\<^sub>j,sb\<^sub>j)"
	  assume conflict: "A \<inter> all_acquired sb\<^sub>j \<noteq> {}"
	  have False
	  proof -
	    from j_bound leq
	    have j_bound': "j < length (map owned ts)"
	      by auto
	    from j_bound have j_bound'': "j < length ts\<^sub>s\<^sub>b"
	      by auto
	    from j_bound' have j_bound''': "j < length ts"
	      by simp
	    
	    from conflict obtain a' where
	      a'_in: "a' \<in> A" and
              a'_in_j: "a' \<in> all_acquired sb\<^sub>j"
	      by auto

	    let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"

	    from ts_sim [rule_format, OF  j_bound''] ts\<^sub>s\<^sub>b_j j_bound''
	    obtain p\<^sub>j suspends\<^sub>j "is\<^sub>s\<^sub>b\<^sub>j" \<theta>\<^sub>s\<^sub>b\<^sub>j \<D>\<^sub>s\<^sub>b\<^sub>j \<R>\<^sub>j \<D>\<^sub>j "is\<^sub>j" where
	      ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j,\<theta>\<^sub>s\<^sub>b\<^sub>j, sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
	      suspends\<^sub>j: "suspends\<^sub>j = ?drop_sb\<^sub>j" and
	      is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
	      \<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
	      ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j, 
	             \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(),   
	             \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	      apply (cases "ts\<^sub>s\<^sub>b!j")
	      apply (force simp add: Let_def)
	      done
	      

	    from a'_in_j all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	    have "a' \<in> all_acquired ?take_sb\<^sub>j \<or> a' \<in> all_acquired suspends\<^sub>j"
	      by (auto simp add: suspends\<^sub>j)
	    thus False
	    proof 
	      assume "a' \<in> all_acquired ?take_sb\<^sub>j"
	      with A_unowned_by_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound a'_in
	      show False
		by (auto dest: all_acquired_unshared_acquired)
	    next
	      assume conflict_drop: "a' \<in> all_acquired suspends\<^sub>j"
	      
	      from split_all_acquired_in [OF conflict_drop]
	      show ?thesis
	      proof
		assume "\<exists>sop a'' v ys zs A L R W. 
                  suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a'' sop v A L R W# zs \<and> a' \<in> A"
		then 
		obtain a'' sop' v' ys zs A' L' R' W' where
		  split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W'# zs" (is "suspends\<^sub>j = ?suspends") and
		  a'_A': "a' \<in> A'"
		  by blast
	    

		from valid_program_history [OF j_bound'' ts\<^sub>s\<^sub>b_j] 
		have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
		then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
		  apply -
		  apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
		  apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		  apply (simp add: split_suspends\<^sub>j)
		  done
		
		from valid_last_prog [OF j_bound'' ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
		then
		have lp: "last_prog p\<^sub>j ?suspends = p\<^sub>j"
		  apply -
		  apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
		  apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		  apply simp
		  done
		
		from valid_reads [OF j_bound'' ts\<^sub>s\<^sub>b_j]
		have reads_consis: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
		from reads_consistent_flush_all_until_volatile_write [OF 
		  \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close>  j_bound''
		  ts\<^sub>s\<^sub>b_j this]
		have reads_consis_m_j: 
		  "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
		  by (simp add: m suspends\<^sub>j)
		
		from outstanding_non_volatile_refs_owned_or_read_only [OF j_bound'' ts\<^sub>s\<^sub>b_j]
		have nvo_j: "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
		with non_volatile_owned_or_read_only_append [of False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		have nvo_take_j: "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j"
		  by auto
		
		from a_unowned_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
		have a_not_acq: "a \<notin> acquired True ?take_sb\<^sub>j \<O>\<^sub>j"
		  by auto
	      
		from a_notin_unforwarded_non_volatile_reads_drop[OF j_bound'' ts\<^sub>s\<^sub>b_j neq_i_j]
		have a_notin_unforwarded_reads: "a \<notin> unforwarded_non_volatile_reads suspends\<^sub>j {}"
		  by (simp add: suspends\<^sub>j)    

		let ?ma="(m(a := f (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m a))))"

		from reads_consistent_mem_eq_on_unforwarded_non_volatile_reads [where W="{}" 
		  and m'="?ma",simplified, OF _ subset_refl reads_consis_m_j] 
		  a_notin_unforwarded_reads
		have reads_consis_ma_j: 
		  "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?ma suspends\<^sub>j"
		  by auto


		from reads_consis_ma_j 
		have reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?ma (ys)"
		  by (simp add: split_suspends\<^sub>j reads_consistent_append)

	    
		from direct_memop_step.RMWWrite [where cond=cond and \<theta>=\<theta>\<^sub>s\<^sub>b and m=m, OF cond']
		have "(RMW a t (D, f) cond ret A L R W# is\<^sub>s\<^sub>b',
		        \<theta>\<^sub>s\<^sub>b, (), m, \<D>, \<O>\<^sub>s\<^sub>b, \<R>\<^sub>s\<^sub>b, \<S>) \<rightarrow> 
                    (is\<^sub>s\<^sub>b', 
		       \<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a)))), (), ?ma, False, \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty, \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".
		from direct_computation.concurrent_step.Memop [OF i_bound' ts_i [simplified sb, simplified] this]
		have step_a: "(ts, m, \<S>) \<Rightarrow>\<^sub>d 
                    (ts[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a)))), (), False, \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)], 
                       ?ma,\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		  (is " _ \<Rightarrow>\<^sub>d (?ts_a, _, ?shared_a)").
	      

		from ts\<^sub>j neq_i_j j_bound 

		have ts_a_j: "?ts_a!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
		  \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), 
		  \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
		  by auto
	    
		
		from valid_write_sops [OF j_bound'' ts\<^sub>s\<^sub>b_j]
		have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
		  by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		  valid_sops_drop: "\<forall>sop\<in>write_sops (ys). valid_sop sop"
		  apply (simp only: write_sops_append)
		  apply auto
		  done
	    
		from read_tmps_distinct [OF j_bound'' ts\<^sub>s\<^sub>b_j]
		have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
		  by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		then obtain 
		  read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
		  distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
		  apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		  apply (simp only: distinct_read_tmps_append)
		  done
	    
		from valid_history [OF j_bound'' ts\<^sub>s\<^sub>b_j]
		have h_consis: 
		  "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
		  apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		  apply simp
		  done
	    
		have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
		proof -
		  from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		    by simp
		  from last_prog_hd_prog_append' [OF h_consis] this
		  have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		    by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		  moreover 
		  have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		    last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		    apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		    by (rule last_prog_hd_prog_append)
		  ultimately show ?thesis
		    by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		qed
	    
		from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
		  h_consis] last_prog_hd_prog
		have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
		  by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		from reads_consistent_drop_volatile_writes_no_volatile_reads  
		[OF reads_consis] 
		have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b (ys) = {}"
		  by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		    split_suspends\<^sub>j )
		from j_bound' have j_bound_ts_a: "j < length ?ts_a" by auto
	    
		from flush_store_buffer_append [where sb="ys" and sb'="Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W'#zs", simplified,
		  OF j_bound_ts_a is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
		  ts_a_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_ys
 		  hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
		  distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
		  no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
		  \<S>="?shared_a"]
	    
		obtain is\<^sub>j' \<R>\<^sub>j' where
		  is\<^sub>j': "Write True a'' sop' A' L' R' W'# instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs" and
		  steps_ys: "(?ts_a, ?ma, ?shared_a)  \<Rightarrow>\<^sub>d\<^sup>* 
		  (?ts_a[j:=(last_prog
                            (hd_prog p\<^sub>j zs) ys,
		             is\<^sub>j',
                             \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps zs),
                             (),
		             \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')],
                  flush ys (?ma),
                  share ys (?shared_a))"
		 (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
		  by (auto simp add: acquired_append)

		from cph
		have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ((ys @ [Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W']) @ zs)"
		  by simp
		from causal_program_history_suffix [OF this]
		have cph': "causal_program_history is\<^sub>s\<^sub>b\<^sub>j zs".	      
		interpret causal\<^sub>j: causal_program_history "is\<^sub>s\<^sub>b\<^sub>j" "zs" by (rule cph')

		from causal\<^sub>j.causal_program_history [of "[]", simplified, OF refl] is\<^sub>j'   
		obtain is\<^sub>j''
		  where is\<^sub>j': "is\<^sub>j' = Write True a'' sop' A' L' R' W'#is\<^sub>j''" and
		  is\<^sub>j'': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j'' @ prog_instrs zs"
		  by clarsimp
		
		from i_bound' have i_bound_ys: "i < length ?ts_ys"
		  by auto
		
		from i_bound' neq_i_j 
		have ts_ys_i: "?ts_ys!i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b',
		  \<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a)))),(), False, \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)"
		  by simp
		
		from j_bound_ts_a have j_bound_ys: "j < length ?ts_ys"
		  by auto
		then have ts_ys_j: "?ts_ys!j = (last_prog (hd_prog p\<^sub>j zs) ys, Write True a'' sop' A' L' R' W'#is\<^sub>j'',
		  \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps zs), (), 
		  \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, 
		  acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')"
		  by (clarsimp simp add: is\<^sub>j')
		note conflict_computation = r_rtranclp_rtranclp [OF step_a steps_ys]
	    
		from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
		have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
		
		
		from safe_delayedE [OF this j_bound_ys ts_ys_j]
		have A'_unowned: 
		  "\<forall>i < length ?ts_ys. j\<noteq>i \<longrightarrow> (let (\<O>\<^sub>i) = map owned ?ts_ys!i in A' \<inter>  \<O>\<^sub>i = {})"
		  apply cases
		  apply (fastforce simp add: Let_def is\<^sub>s\<^sub>b)+
		  done
		from a'_in a'_A' A'_unowned [rule_format, of i] neq_i_j i_bound' A_R
		show False
		  by (auto simp add: Let_def)
	      next
		assume "\<exists>A L R W ys zs. suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a' \<in> A"
		then 
		obtain ys zs A' L' R' W' where
		  split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs" (is "suspends\<^sub>j = ?suspends") and
		  a'_A': "a' \<in> A'"
		  by blast
	    

		from valid_program_history [OF j_bound'' ts\<^sub>s\<^sub>b_j] 
		have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
		then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
		  apply -
		  apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
		  apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		  apply (simp add: split_suspends\<^sub>j)
		  done
		
		from valid_last_prog [OF j_bound'' ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
		then
		have lp: "last_prog p\<^sub>j ?suspends = p\<^sub>j"
		  apply -
		  apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
		  apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		  apply simp
		  done
		
		
		from valid_reads [OF j_bound'' ts\<^sub>s\<^sub>b_j]
		have reads_consis: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
		from reads_consistent_flush_all_until_volatile_write [OF 
		  \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close>  j_bound''
		  ts\<^sub>s\<^sub>b_j this]
		have reads_consis_m_j: 
		  "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
		  by (simp add: m suspends\<^sub>j)
		
		from outstanding_non_volatile_refs_owned_or_read_only [OF j_bound'' ts\<^sub>s\<^sub>b_j]
		have nvo_j: "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
		with non_volatile_owned_or_read_only_append [of False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		have nvo_take_j: "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j"
		  by auto
		
		from a_unowned_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
		have a_not_acq: "a \<notin> acquired True ?take_sb\<^sub>j \<O>\<^sub>j"
		  by auto
	      
		from a_notin_unforwarded_non_volatile_reads_drop[OF j_bound'' ts\<^sub>s\<^sub>b_j neq_i_j]
		have a_notin_unforwarded_reads: "a \<notin> unforwarded_non_volatile_reads suspends\<^sub>j {}"
		  by (simp add: suspends\<^sub>j)    

		let ?ma="(m(a := f (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m a))))"

		from reads_consistent_mem_eq_on_unforwarded_non_volatile_reads [where W="{}" 
		  and m'="?ma",simplified, OF _ subset_refl reads_consis_m_j] 
		  a_notin_unforwarded_reads
		have reads_consis_ma_j: 
		  "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?ma suspends\<^sub>j"
		  by auto


		from reads_consis_ma_j 
		have reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?ma (ys)"
		  by (simp add: split_suspends\<^sub>j reads_consistent_append)
	    
		from direct_memop_step.RMWWrite [where cond=cond and \<theta>=\<theta>\<^sub>s\<^sub>b and m=m, OF cond']
		have "(RMW a t (D, f) cond ret A L R W# is\<^sub>s\<^sub>b', 
		        \<theta>\<^sub>s\<^sub>b, (), m, \<D>,\<O>\<^sub>s\<^sub>b,  \<R>\<^sub>s\<^sub>b, \<S>) \<rightarrow> 
                    (is\<^sub>s\<^sub>b', 
                        \<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a)))), (), ?ma, False, \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty,\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".
		from direct_computation.concurrent_step.Memop [OF i_bound' ts_i [simplified sb, simplified] this]
		have step_a: "(ts, m, \<S>) \<Rightarrow>\<^sub>d 
                    (ts[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a)))), (), False, \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)], 
                      ?ma,\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		  (is " _ \<Rightarrow>\<^sub>d (?ts_a, _, ?shared_a)").
	      

		from ts\<^sub>j neq_i_j j_bound 

		have ts_a_j: "?ts_a!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
		  \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
		  by auto
	    
		
		from valid_write_sops [OF j_bound'' ts\<^sub>s\<^sub>b_j]
		have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
		  by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		  valid_sops_drop: "\<forall>sop\<in>write_sops (ys). valid_sop sop"
		  apply (simp only: write_sops_append)
		  apply auto
		  done
	    
		from read_tmps_distinct [OF j_bound'' ts\<^sub>s\<^sub>b_j]
		have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
		  by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		then obtain 
		  read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
		  distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
		  apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		  apply (simp only: distinct_read_tmps_append)
		  done
	    
		from valid_history [OF j_bound'' ts\<^sub>s\<^sub>b_j]
		have h_consis: 
		  "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
		  apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		  apply simp
		  done
	    
		have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
		proof -
		  from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		    by simp
		  from last_prog_hd_prog_append' [OF h_consis] this
		  have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		    by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		  moreover 
		  have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		    last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		    apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		    by (rule last_prog_hd_prog_append)
		  ultimately show ?thesis
		    by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		qed
	    
		from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
		  h_consis] last_prog_hd_prog
		have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
		  by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		from reads_consistent_drop_volatile_writes_no_volatile_reads  
		[OF reads_consis] 
		have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b (ys) = {}"
		  by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		    split_suspends\<^sub>j )
		from j_bound' have j_bound_ts_a: "j < length ?ts_a" by auto
	    
		from flush_store_buffer_append [where sb="ys" and sb'="Ghost\<^sub>s\<^sub>b A' L' R' W'#zs", simplified,
		  OF j_bound_ts_a is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
		  ts_a_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_ys
 		  hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
		  distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
		  no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
		  \<S>="?shared_a"]
	    
		obtain is\<^sub>j' \<R>\<^sub>j' where
		  is\<^sub>j': "Ghost A' L' R' W'# instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs" and
		  steps_ys: "(?ts_a, ?ma, ?shared_a)  \<Rightarrow>\<^sub>d\<^sup>* 
		  (?ts_a[j:=(last_prog
                            (hd_prog p\<^sub>j zs) ys,
		             is\<^sub>j',
                             \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps zs),
                             (),
		             \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')],
                  flush ys (?ma),
                  share ys (?shared_a))"
		 (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
		 by (auto simp add: acquired_append)

	       from cph
	       have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ((ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W']) @ zs)"
		 by simp
	       from causal_program_history_suffix [OF this]
	       have cph': "causal_program_history is\<^sub>s\<^sub>b\<^sub>j zs".	      
	       interpret causal\<^sub>j: causal_program_history "is\<^sub>s\<^sub>b\<^sub>j" "zs" by (rule cph')

	       from causal\<^sub>j.causal_program_history [of "[]", simplified, OF refl] is\<^sub>j'   
	       obtain is\<^sub>j''
		 where is\<^sub>j': "is\<^sub>j' = Ghost A' L' R' W'#is\<^sub>j''" and
		 is\<^sub>j'': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j'' @ prog_instrs zs"
		 by clarsimp
	       
	       from i_bound' have i_bound_ys: "i < length ?ts_ys"
		 by auto
	       
	       from i_bound' neq_i_j 
	       have ts_ys_i: "?ts_ys!i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b',
		 \<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a)))),(), False, \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)"
		 by simp
	    
	       from j_bound_ts_a have j_bound_ys: "j < length ?ts_ys"
		 by auto
	       then have ts_ys_j: "?ts_ys!j = (last_prog (hd_prog p\<^sub>j zs) ys, Ghost A' L' R' W'#is\<^sub>j'',
		 \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps zs), (), 
		 \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, 
		 acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')"
		 by (clarsimp simp add: is\<^sub>j')
	       note conflict_computation = r_rtranclp_rtranclp [OF step_a steps_ys]
	    
	       from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	       have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	       

	       from safe_delayedE [OF this j_bound_ys ts_ys_j]
	       have A'_unowned: 
		 "\<forall>i < length ?ts_ys. j\<noteq>i \<longrightarrow> (let (\<O>\<^sub>i) = map owned ?ts_ys!i in A' \<inter>  \<O>\<^sub>i = {})"
		 apply cases
		 apply (fastforce simp add: Let_def is\<^sub>s\<^sub>b)+
		 done
	       from a'_in a'_A' A'_unowned [rule_format, of i] neq_i_j i_bound' A_R
	       show False
		 by (auto simp add: Let_def)
	     qed
	   qed
	 qed
	}
	thus ?thesis
	  by (auto simp add: Let_def)
      qed



      {
	fix j 
	fix p\<^sub>j is\<^sub>s\<^sub>b\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>s\<^sub>b\<^sub>j \<theta>\<^sub>j sb\<^sub>j
	assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	assume ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b!j=(p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	assume neq_i_j: "i\<noteq>j"
	have "A \<inter> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j) 
	           (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) = {}"
	proof -
	  {
	    let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    
	    assume conflict: "A \<inter> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j \<noteq> {}"
	    have False
	    proof -
	      from conflict obtain a' where
		a'_in: "a' \<in> A" and
		a'_in_j: "a' \<in> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
		by auto
	      
	      
	      from ts_sim [rule_format, OF  j_bound] ts\<^sub>s\<^sub>b_j j_bound
	      obtain p\<^sub>j suspends\<^sub>j "is\<^sub>s\<^sub>b\<^sub>j" \<D>\<^sub>s\<^sub>b\<^sub>j \<D>\<^sub>j \<theta>\<^sub>s\<^sub>b\<^sub>j "is\<^sub>j" where
		ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j, \<theta>\<^sub>s\<^sub>b\<^sub>j, sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
		suspends\<^sub>j: "suspends\<^sub>j = ?drop_sb\<^sub>j" and
		is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
		\<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
		ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
	        \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
		apply (cases "ts\<^sub>s\<^sub>b!j")
		apply (clarsimp simp add: Let_def)
		done
	      from split_in_read_only_reads [OF a'_in_j [simplified suspends\<^sub>j [symmetric]]]
	      obtain t' v' ys zs where
		split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Read\<^sub>s\<^sub>b False a' t' v'# zs" (is "suspends\<^sub>j = ?suspends") and
		a'_unacq: "a' \<notin> acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)"
		by blast

	      from valid_program_history [OF j_bound ts\<^sub>s\<^sub>b_j] 
	      have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	      then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
		apply -
		apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply (simp add: split_suspends\<^sub>j)
		done

	      from valid_last_prog [OF j_bound ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	      then
	      have lp: "last_prog p\<^sub>j ?suspends = p\<^sub>j"
		apply -
		apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply simp
		done

	      from valid_reads [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have reads_consis: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	      from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> 
		j_bound
		ts\<^sub>s\<^sub>b_j this]
	      have reads_consis_m_j: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
		by (simp add: m suspends\<^sub>j)

	      from outstanding_non_volatile_refs_owned_or_read_only [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have nvo_j: "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	      with non_volatile_owned_or_read_only_append [of False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	      have nvo_take_j: "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j"
		by auto

	      from a_unowned_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
	      have a_not_acq: "a \<notin> acquired True ?take_sb\<^sub>j \<O>\<^sub>j"
		by auto

	      from a_notin_unforwarded_non_volatile_reads_drop[OF j_bound ts\<^sub>s\<^sub>b_j neq_i_j]
	      have a_notin_unforwarded_reads: "a \<notin> unforwarded_non_volatile_reads suspends\<^sub>j {}"
		by (simp add: suspends\<^sub>j)
	      
	      let ?ma="(m(a := f (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m a))))"

	      from reads_consistent_mem_eq_on_unforwarded_non_volatile_reads [where W="{}" 
		and m'="?ma",simplified, OF _ subset_refl reads_consis_m_j] 
		a_notin_unforwarded_reads
	      have reads_consis_ma_j: 
		"reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?ma suspends\<^sub>j"
		by auto

	      from reads_consis_ma_j 
	      have reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?ma (ys)"
		by (simp add: split_suspends\<^sub>j reads_consistent_append)

	      from direct_memop_step.RMWWrite [where cond=cond and \<theta>=\<theta>\<^sub>s\<^sub>b and m=m, OF cond' ]
	      have "(RMW a t (D, f) cond ret A L R W# is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), m, \<D>,\<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b,\<S>) \<rightarrow> 
                (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a)))), (), ?ma, False, \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty, \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".
	      from direct_computation.concurrent_step.Memop [OF i_bound' ts_i  this] 
	      have step_a: "(ts, m, \<S>) \<Rightarrow>\<^sub>d 
                (ts[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a)))), (), False, \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)], 
                ?ma,\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		(is " _ \<Rightarrow>\<^sub>d (?ts_a, _, ?shared_a)").

	      from ts\<^sub>j neq_i_j j_bound 

	      have ts_a_j: "?ts_a!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
		\<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
		by auto


	      from valid_write_sops [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		valid_sops_drop: "\<forall>sop\<in>write_sops (ys). valid_sop sop"
		apply (simp only: write_sops_append)
		apply auto
		done

	      from read_tmps_distinct [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      then obtain 
		read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
		distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		apply (simp only: distinct_read_tmps_append)
		done
	      
	      from valid_history [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have h_consis: 
		"history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply simp
		done
	      
	      have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	      proof -
		from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		  by simp
		from last_prog_hd_prog_append' [OF h_consis] this
		have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		  by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		moreover 
		have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		  last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		  apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		  by (rule last_prog_hd_prog_append)
		ultimately show ?thesis
		  by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      qed

	      from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
		h_consis] last_prog_hd_prog
	      have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      from reads_consistent_drop_volatile_writes_no_volatile_reads  
	      [OF reads_consis] 
	      have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b (ys) = {}"
		by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		  split_suspends\<^sub>j )

	      from j_bound leq have j_bound_ts_a: "j < length ?ts_a" by auto
	      

	      
	      from flush_store_buffer_append [where sb="ys" and sb'="Read\<^sub>s\<^sub>b False a' t' v'#zs", simplified,
		OF j_bound_ts_a is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
		ts_a_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_ys
 		hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
		distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
		no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
		\<S>="?shared_a"]

	      obtain is\<^sub>j' \<R>\<^sub>j' where
		is\<^sub>j': "Read False a' t'# instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs" and
		steps_ys: "(?ts_a, ?ma, ?shared_a)  \<Rightarrow>\<^sub>d\<^sup>* 
		(?ts_a[j:=(last_prog
                (hd_prog p\<^sub>j zs) ys,
		is\<^sub>j',
                \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - insert t' (read_tmps zs)),
                (), \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')],
                flush ys (?ma),
                share ys (?shared_a))"
		(is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
		by (auto simp add: acquired_append)

	      from cph
	      have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ((ys @ [Read\<^sub>s\<^sub>b False a' t' v']) @ zs)"
		by simp
	      from causal_program_history_suffix [OF this]
	      have cph': "causal_program_history is\<^sub>s\<^sub>b\<^sub>j zs".	      
	      interpret causal\<^sub>j: causal_program_history "is\<^sub>s\<^sub>b\<^sub>j" "zs" by (rule cph')

	      from causal\<^sub>j.causal_program_history [of "[]", simplified, OF refl] is\<^sub>j'   
	      obtain is\<^sub>j''
		where is\<^sub>j': "is\<^sub>j' = Read False a' t'#is\<^sub>j''" and
		is\<^sub>j'': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j'' @ prog_instrs zs"
		by clarsimp
	      
	      from i_bound' have i_bound_ys: "i < length ?ts_ys"
		by auto

	      from i_bound' neq_i_j 
	      have ts_ys_i: "?ts_ys!i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', 
		\<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a)))),(), False, \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)"
		by simp

	      from j_bound_ts_a have j_bound_ys: "j < length ?ts_ys"
		by auto
	      then have ts_ys_j: "?ts_ys!j = (last_prog (hd_prog p\<^sub>j zs) ys, Read False a' t'#is\<^sub>j'', \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - insert t' (read_tmps zs)), (), \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, 
		acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')"
		by (clarsimp simp add: is\<^sub>j')
	      note conflict_computation = r_rtranclp_rtranclp [OF step_a steps_ys]
	      
	      from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	      have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".


	      from safe_delayedE [OF this j_bound_ys ts_ys_j]
	      
	      have "a' \<in> acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<or>
		a' \<in> read_only (share ys (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
		apply cases
		apply (auto simp add: Let_def is\<^sub>s\<^sub>b)
		done

	      with a'_unacq
	      have a'_ro: "a' \<in> read_only (share ys (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
		by auto
	      from a'_in
	      have a'_not_ro: "a' \<notin> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		by (auto simp add:  in_read_only_convs)

	      have "a' \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	      proof -
		{
		  assume a_notin: "a' \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
		  from weak_sharing_consis [OF j_bound ts\<^sub>s\<^sub>b_j]
		  have "weak_sharing_consistent \<O>\<^sub>j sb\<^sub>j".
		  with weak_sharing_consistent_append [of \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		  have "weak_sharing_consistent (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) suspends\<^sub>j"
		    by (auto simp add: suspends\<^sub>j)
		  with split_suspends\<^sub>j
		  have weak_consis: "weak_sharing_consistent (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ys"
		    by (simp add: weak_sharing_consistent_append)
		  from all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		  have "all_acquired ys \<subseteq> all_acquired sb\<^sub>j"
		    apply (clarsimp)
		    apply (clarsimp simp add: suspends\<^sub>j [symmetric] split_suspends\<^sub>j all_acquired_append)
		    done
	          with a_notin acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b [of sb\<^sub>j \<O>\<^sub>j]
                    all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		  have "a' \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j \<union> all_acquired ys"
                    by auto
                
		  from read_only_share_unowned [OF weak_consis this a'_ro] 
		  have "a' \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" .
		  
		  with a'_not_ro have False
		    by auto	  
		  with a_notin read_only_share_unowned [OF weak_consis _ a'_ro] 
		    all_acquired_takeWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" sb\<^sub>j]

		  have "a' \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		    by (auto simp add: acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)
		  with a'_not_ro have False
		    by auto
		}
		thus ?thesis by blast
	      qed
	      
	      moreover
	      from A_unacquired_by_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
	      have "A \<inter> all_acquired sb\<^sub>j = {}"
		by (auto simp add: Let_def)
	      moreover
	      from A_unowned_by_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
	      have "A \<inter> \<O>\<^sub>j = {}"
	        by (auto simp add: Let_def dest: all_shared_acquired_in)
	      moreover note a'_in
	      ultimately
	      show False
		by auto
	    qed
	  }
	  thus ?thesis
	    by (auto simp add: Let_def)
	qed
      } note A_no_read_only_reads = this	      
	    
      have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof 
	  fix j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j p\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume ts\<^sub>s\<^sub>b'_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b' \<O>\<^sub>j sb\<^sub>j"
	  proof (cases "j=i")
	    case True
	    have "non_volatile_owned_or_read_only False 
	      (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O>\<^sub>s\<^sub>b \<union> A - R) []"
	      by simp
	    then show ?thesis
	      using True i_bound ts\<^sub>s\<^sub>b'_j
	      by (auto simp add: ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' sb sb')
	  next
	    case False
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    with ts\<^sub>s\<^sub>b'_j False i_bound 
	    have ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')


	    note nvo = outstanding_non_volatile_refs_owned_or_read_only [OF j_bound' ts\<^sub>s\<^sub>b_j]

	    from read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] R_owned
	    have "R \<inter> read_only \<S>\<^sub>s\<^sub>b = {}"
	      by auto
	    with A_no_read_only_reads [OF j_bound' ts\<^sub>s\<^sub>b_j False [symmetric]] L_subset
	    have "\<forall>a\<in>read_only_reads
	      (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j)
	      (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j).
		a \<in> read_only \<S>\<^sub>s\<^sub>b \<longrightarrow> a \<in> read_only (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	      by (auto simp add: in_read_only_convs)
	    from non_volatile_owned_or_read_only_read_only_reads_eq' [OF nvo this]
	    have "non_volatile_owned_or_read_only False (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<O>\<^sub>j sb\<^sub>j".
	    thus ?thesis by (simp add: \<S>\<^sub>s\<^sub>b')
	  qed
	qed
      next
	show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)
	  fix i\<^sub>1 j p\<^sub>1 "is\<^sub>1" \<O>\<^sub>1 \<R>\<^sub>1 \<D>\<^sub>1 xs\<^sub>1 sb\<^sub>1 p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume i\<^sub>1_bound: "i\<^sub>1 < length ts\<^sub>s\<^sub>b'"
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume i\<^sub>1_j: "i\<^sub>1 \<noteq> j"
	  assume ts_i\<^sub>1: "ts\<^sub>s\<^sub>b'!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	  assume ts_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}"
	  proof (cases "i\<^sub>1=i")
	    case True
	    with ts_i\<^sub>1 i_bound show ?thesis
	      by (simp add: ts\<^sub>s\<^sub>b' sb' sb)
	  next
	    case False
	    note i\<^sub>1_i = this
	    from i\<^sub>1_bound have i\<^sub>1_bound': "i\<^sub>1 < length ts\<^sub>s\<^sub>b"
	      by (simp add: ts\<^sub>s\<^sub>b' sb' sb)
	    hence i\<^sub>1_bound'': "i\<^sub>1 < length (map owned ts\<^sub>s\<^sub>b)"
	      by auto
	    from ts_i\<^sub>1 False have ts_i\<^sub>1': "ts\<^sub>s\<^sub>b!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	      by (simp add: ts\<^sub>s\<^sub>b' sb' sb)
	    show ?thesis
	    proof (cases "j=i")
	      case True

	      from i_bound ts_j ts\<^sub>s\<^sub>b' True have sb\<^sub>j: "sb\<^sub>j=[]"
		by (simp add: ts\<^sub>s\<^sub>b' sb')
	      from A_unused_by_others [rule_format, OF _ False [symmetric]] ts_i\<^sub>1 i\<^sub>1_bound''
		False i\<^sub>1_bound'
	      have "A \<inter> (\<O>\<^sub>1 \<union> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1) = {}"
		by (auto simp add: Let_def ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' owned_def)
	      moreover
	      from outstanding_volatile_writes_unowned_by_others 
	      [OF i\<^sub>1_bound' i_bound i\<^sub>1_i ts_i\<^sub>1' ts\<^sub>s\<^sub>b_i]
	      have "\<O>\<^sub>s\<^sub>b \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}" by (simp add: sb)
	      
	      ultimately show ?thesis using ts_j True 
		by (auto simp add: i_bound ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb\<^sub>j)
	    next
	      case False
	      from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from ts_j False have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from outstanding_volatile_writes_unowned_by_others 
              [OF i\<^sub>1_bound' j_bound' i\<^sub>1_j ts_i\<^sub>1' ts_j']
	      show "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}" .
	    qed
	  qed
	qed
      next
	show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
	proof 
	  fix n m
	  fix p\<^sub>n "is\<^sub>n" \<O>\<^sub>n \<R>\<^sub>n \<D>\<^sub>n \<theta>\<^sub>n sb\<^sub>n p\<^sub>m "is\<^sub>m" \<O>\<^sub>m \<R>\<^sub>m \<D>\<^sub>m \<theta>\<^sub>m sb\<^sub>m
	  assume n_bound: "n < length ts\<^sub>s\<^sub>b'"
	    and m_bound: "m < length ts\<^sub>s\<^sub>b'"
	    and neq_n_m: "n\<noteq>m"
	    and nth: "ts\<^sub>s\<^sub>b'!n = (p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
	    and mth: "ts\<^sub>s\<^sub>b'!m =(p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m,\<R>\<^sub>m)"
	  from n_bound have n_bound': "n < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')
	  from m_bound have m_bound': "m < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')
	  show "(\<O>\<^sub>m \<union> all_acquired sb\<^sub>m) \<inter>
            read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) \<O>\<^sub>n)
            (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) =
            {}"
	  proof (cases "m=i")
	    case True
	    with neq_n_m have neq_n_i: "n\<noteq>i"
	      by auto
	    
	    with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    note read_only_reads_unowned [OF n_bound' i_bound  neq_n_i nth' ts\<^sub>s\<^sub>b_i]
	    moreover
	    note A_no_read_only_reads [OF n_bound' nth']
	    ultimately
	    show ?thesis
	      using True ts\<^sub>s\<^sub>b_i neq_n_i nth mth n_bound' m_bound'
	      by (auto simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb sb')
	  next
	    case False
	    note neq_m_i = this
	    with m_bound mth i_bound have mth': "ts\<^sub>s\<^sub>b!m = (p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m,\<R>\<^sub>m)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    show ?thesis
	    proof (cases "n=i")
	      case True
	      with ts\<^sub>s\<^sub>b_i nth mth neq_m_i n_bound' 
	      show ?thesis
		by (auto simp add: ts\<^sub>s\<^sub>b'  sb')
	    next
	      case False
	      with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      from read_only_reads_unowned [OF n_bound' m_bound' neq_n_m  nth' mth'] False neq_m_i
	      show ?thesis 
		by (clarsimp)
	    qed
	  qed
	qed
      next
	show "ownership_distinct ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)
	  fix i\<^sub>1 j p\<^sub>1 "is\<^sub>1" \<O>\<^sub>1 \<R>\<^sub>1 \<D>\<^sub>1 xs\<^sub>1 sb\<^sub>1 p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume i\<^sub>1_bound: "i\<^sub>1 < length ts\<^sub>s\<^sub>b'"
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume i\<^sub>1_j: "i\<^sub>1 \<noteq> j"
	  assume ts_i\<^sub>1: "ts\<^sub>s\<^sub>b'!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	  assume ts_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "(\<O>\<^sub>1 \<union> all_acquired sb\<^sub>1) \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j)= {}"
	  proof (cases "i\<^sub>1=i")
	    case True
	    with i\<^sub>1_j have i_j: "i\<noteq>j" 
	      by simp
	    
	    from i_bound ts_i\<^sub>1 ts\<^sub>s\<^sub>b' True have sb\<^sub>1: "sb\<^sub>1=[]"
	      by (simp add: ts\<^sub>s\<^sub>b' sb')
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    hence j_bound'': "j < length (map owned ts\<^sub>s\<^sub>b)"
	      by simp	    
	    from ts_j i_j have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    
	    from A_unused_by_others [rule_format, OF _ i_j] ts_j i_j j_bound'
	    have "A \<inter> (\<O>\<^sub>j \<union> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j) = {}"
	      by (auto simp add: Let_def ts\<^sub>s\<^sub>b' owned_def)
	    moreover
	    from A_unacquired_by_others [rule_format, OF _ i_j] ts_j i_j j_bound'
	    have "A \<inter> all_acquired sb\<^sub>j = {}"
	      by (auto simp add: Let_def ts\<^sub>s\<^sub>b')
(*
	    from a_not_acquired_others [rule_format, OF j_bound'' i_j] ts_j i_j j_bound'
	    have "a \<notin> all_acquired sb\<^sub>j"
	      by (auto simp add: Let_def ts\<^sub>s\<^sub>b')
*)
	    moreover
	    from ownership_distinct [OF i_bound j_bound' i_j ts\<^sub>s\<^sub>b_i ts_j']
	    have "\<O>\<^sub>s\<^sub>b \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j)= {}" by (simp add: sb)
	    ultimately show ?thesis using ts_i\<^sub>1 True
	      by (auto simp add: i_bound ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' sb\<^sub>1)
	  next
	    case False
	    note i\<^sub>1_i = this
	    from i\<^sub>1_bound have i\<^sub>1_bound': "i\<^sub>1 < length ts\<^sub>s\<^sub>b"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    hence i\<^sub>1_bound'': "i\<^sub>1 < length (map owned ts\<^sub>s\<^sub>b)"
	      by simp	    
	    from ts_i\<^sub>1 False have ts_i\<^sub>1': "ts\<^sub>s\<^sub>b!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    show ?thesis
	    proof (cases "j=i")
	      case True
	      from A_unused_by_others [rule_format, OF _ False [symmetric]] ts_i\<^sub>1  
		False i\<^sub>1_bound'
	      have "A \<inter> (\<O>\<^sub>1 \<union> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1) = {}"
		by (auto simp add: Let_def ts\<^sub>s\<^sub>b' owned_def)
	      moreover
	      from A_unacquired_by_others [rule_format, OF _ False [symmetric]] ts_i\<^sub>1  False i\<^sub>1_bound'
	      have "A \<inter> all_acquired sb\<^sub>1 = {}"
		by (auto simp add: Let_def ts\<^sub>s\<^sub>b' owned_def)
	      moreover
	      from ownership_distinct [OF i\<^sub>1_bound' i_bound i\<^sub>1_i ts_i\<^sub>1' ts\<^sub>s\<^sub>b_i]
	      have "(\<O>\<^sub>1 \<union> all_acquired sb\<^sub>1) \<inter> \<O>\<^sub>s\<^sub>b = {}" by (simp add: sb)
	      ultimately show ?thesis
		using ts_j True
		by (auto simp add: i_bound ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb')
	    next
	      case False
	      from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from ts_j False have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from ownership_distinct [OF i\<^sub>1_bound' j_bound' i\<^sub>1_j ts_i\<^sub>1' ts_j']
	      show "(\<O>\<^sub>1 \<union> all_acquired sb\<^sub>1) \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {}" .
	    qed
	  qed
	qed
      qed

      have valid_hist': "valid_history program_step ts\<^sub>s\<^sub>b'"
      proof -
	from valid_history [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "history_consistent (\<theta>\<^sub>s\<^sub>b(t\<mapsto>ret (m\<^sub>s\<^sub>b a) (f (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m\<^sub>s\<^sub>b a))))) (hd_prog p\<^sub>s\<^sub>b []) []" by simp
	from valid_history_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb' sb)
      qed

      from valid_reads [OF i_bound ts\<^sub>s\<^sub>b_i]
      have reads_consis: "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b sb" .

      have valid_reads': "valid_reads m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (unfold_locales)
	fix j p\<^sub>j "is\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j acq\<^sub>j \<theta>\<^sub>j sb\<^sub>j
	assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	assume ts_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	show "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b' sb\<^sub>j"
	proof (cases "i=j")
	  case True
	  from reads_consis ts_j j_bound sb show ?thesis
	    by (clarsimp simp add: True  m\<^sub>s\<^sub>b' Write\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b' sb')
	next
	  case False
	  from j_bound have j_bound':  "j < length ts\<^sub>s\<^sub>b"
	    by (simp add: ts\<^sub>s\<^sub>b')
	  moreover from ts_j False have ts_j': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	    using j_bound by (simp add: ts\<^sub>s\<^sub>b')
	  ultimately have consis_m: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j"
	    by (rule valid_reads)
	  let ?m' = "(m\<^sub>s\<^sub>b(a := f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m\<^sub>s\<^sub>b a))))"
	  from a_unowned_others [rule_format, OF _ False] j_bound' ts_j'
          obtain a_acq: "a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j" and
          a_unsh: "a \<notin> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
            by auto
          with a_notin_unforwarded_non_volatile_reads_drop [OF j_bound' ts_j' False]
	  have "\<forall>a\<in>acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j \<union> 
                   all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<union> 
	           unforwarded_non_volatile_reads (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) {}. 
	    ?m' a = m\<^sub>s\<^sub>b a"
	    by auto
	  from reads_consistent_mem_eq_on_unforwarded_non_volatile_reads_drop 
	  [where W="{}",simplified, OF this _ _ consis_m] 
	    acquired_reads_all_acquired' [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" \<O>\<^sub>j]
	  have "reads_consistent False \<O>\<^sub>j (m\<^sub>s\<^sub>b(a := f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m\<^sub>s\<^sub>b a)))) sb\<^sub>j"
	    by (auto simp del: fun_upd_apply)
	  thus ?thesis 
	    by (simp add: m\<^sub>s\<^sub>b')
	qed
      qed

      have valid_sharing': "valid_sharing (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
      proof (intro_locales)	
	show "outstanding_non_volatile_writes_unshared (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)
	  fix j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j acq\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume jth: "ts\<^sub>s\<^sub>b' ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "non_volatile_writes_unshared (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)  sb\<^sub>j"
	  proof (cases "i=j")
	    case True
	    with i_bound jth show ?thesis
	      by (simp add: ts\<^sub>s\<^sub>b' sb' sb)
	  next
	    case False
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    from jth False have jth': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    from outstanding_non_volatile_writes_unshared [OF j_bound' jth']
	    have unshared: "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b sb\<^sub>j".
	    have "\<forall>a\<in>dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom \<S>\<^sub>s\<^sub>b. a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
	    proof -
	      { 
		fix a 
		assume a_in: "a \<in> dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom \<S>\<^sub>s\<^sub>b"
		hence a_R: "a \<in> R"
		  by clarsimp
		assume a_in_j: "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
		have False
		proof -
		  from non_volatile_owned_or_read_only_outstanding_non_volatile_writes [OF
		  outstanding_non_volatile_refs_owned_or_read_only [OF j_bound' jth']]
		  a_in_j
		  have "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
		    by auto
		  moreover
		  with ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth'] a_R R_owned
		  show False
		    by blast
		qed
	      }
	      thus ?thesis by blast
	    qed
		 
	    from non_volatile_writes_unshared_no_outstanding_non_volatile_Write\<^sub>s\<^sub>b 
	    [OF unshared this]
	    show ?thesis .
	  qed
	qed
      next
	show "sharing_consis (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)  
	  fix j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j acq\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume jth: "ts\<^sub>s\<^sub>b' ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "sharing_consistent (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<O>\<^sub>j sb\<^sub>j"
	  proof (cases "i=j")
	    case True
	    with i_bound jth show ?thesis
	      by (simp add: ts\<^sub>s\<^sub>b' sb' sb)
	  next
	    case False
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    from jth False have jth': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    from sharing_consis [OF j_bound' jth']
	    have consis: "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".

	    have acq_cond: "all_acquired sb\<^sub>j \<inter> dom \<S>\<^sub>s\<^sub>b - dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	    proof -
	      {
		fix a
		assume a_acq: "a \<in> all_acquired sb\<^sub>j" 
		assume "a \<in> dom \<S>\<^sub>s\<^sub>b" 
		assume a_L: "a \<in> L"
		have False
		proof -
		  from A_unacquired_by_others [rule_format, of j,OF _ False] j_bound' jth'
		  have "A \<inter> all_acquired sb\<^sub>j = {}"
		    by auto
		  with a_acq a_L L_subset
		  show False
		    by blast
		qed
	      }
	      thus ?thesis
		by auto
	    qed
	    have uns_cond: "all_unshared sb\<^sub>j \<inter> dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom \<S>\<^sub>s\<^sub>b = {}"
	    proof -
	      {
		fix a
		assume a_uns: "a \<in> all_unshared sb\<^sub>j" 
		assume "a \<notin> L" 
		assume a_R:  "a \<in> R"
		have False
		proof -
		  from unshared_acquired_or_owned [OF consis] a_uns
		  have "a \<in> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j" by auto
		  with ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth']  R_owned a_R
		  show False
		    by blast
		qed
	      }
	      thus ?thesis
		by auto
	    qed

	    from sharing_consistent_preservation [OF consis acq_cond uns_cond]
	    show ?thesis
	      by (simp add: ts\<^sub>s\<^sub>b')
	  qed
	qed
      next
	show "unowned_shared (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)
	  show "- \<Union>((\<lambda>(_,_, _, _,_, \<O>,_). \<O>) ` set ts\<^sub>s\<^sub>b') \<subseteq> dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	  proof -

	    have s: "\<Union>((\<lambda>(_,_, _, _,_, \<O>,_). \<O>) ` set ts\<^sub>s\<^sub>b') =
              \<Union>((\<lambda>(_,_, _, _,_, \<O>,_). \<O>) ` set ts\<^sub>s\<^sub>b) \<union> A - R"
	      
	      apply (unfold ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b') 
	      apply (rule acquire_release_ownership_nth_update [OF R_owned i_bound ts\<^sub>s\<^sub>b_i])
	      apply fact
	      done

	    note unowned_shared L_subset A_R
	    then
	    show ?thesis
	      apply (simp only: s)
	      apply auto
	      done
	  qed
	qed
      next
	show "read_only_unowned (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	proof 
	  fix j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j acq\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume jth: "ts\<^sub>s\<^sub>b' ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "\<O>\<^sub>j \<inter> read_only (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	  proof (cases "i=j")
	    case True
	    from read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] R_owned  A_R 
	    have "(\<O>\<^sub>s\<^sub>b \<union> A - R) \<inter> read_only (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	      by (auto simp add: in_read_only_convs )
	    with jth ts\<^sub>s\<^sub>b_i i_bound True
	    show ?thesis
	      by (auto simp add: \<O>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b')
	  next
	    case False
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    with False jth have jth': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    from read_only_unowned [OF j_bound' jth']
	    have "\<O>\<^sub>j \<inter> read_only \<S>\<^sub>s\<^sub>b = {}".
	    moreover
	    from A_unowned_by_others [rule_format, OF _ False] j_bound' jth'
	    have "A \<inter> \<O>\<^sub>j = {}"
	      by (auto dest: all_shared_acquired_in )
	    moreover
	    from ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth']
	    have "\<O>\<^sub>s\<^sub>b \<inter> \<O>\<^sub>j = {}"
	      by auto
	    moreover note R_owned A_R
	    ultimately show ?thesis
	      by (fastforce simp add: in_read_only_convs split: if_split_asm)
	  qed
	qed
      next
	show "no_outstanding_write_to_read_only_memory (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	proof 
	  fix j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j acq\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume jth: "ts\<^sub>s\<^sub>b' ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "no_write_to_read_only_memory (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) sb\<^sub>j"
	  proof (cases "i=j")
	    case True
	    with jth ts\<^sub>s\<^sub>b_i i_bound 
	    show ?thesis
	      by (auto simp add: sb sb' ts\<^sub>s\<^sub>b')
	  next
	    case False
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    with False jth have jth': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    from no_outstanding_write_to_read_only_memory [OF j_bound' jth']
	    have nw: "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b sb\<^sub>j".
	    have "R \<inter> outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>j = {}"
	    proof -
	      note dist = ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth']
	      from non_volatile_owned_or_read_only_outstanding_non_volatile_writes 
	      [OF outstanding_non_volatile_refs_owned_or_read_only [OF j_bound' jth']]
		dist
	      have "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<inter> \<O>\<^sub>s\<^sub>b = {}"
		by auto
	      moreover
	      from outstanding_volatile_writes_unowned_by_others [OF j_bound'  i_bound 
		False [symmetric] jth' ts\<^sub>s\<^sub>b_i ]
	      have "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<inter> \<O>\<^sub>s\<^sub>b = {}" 
		by auto
	      ultimately have "outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>j \<inter> \<O>\<^sub>s\<^sub>b = {}" 
		by (auto simp add: misc_outstanding_refs_convs)
	      with R_owned
	      show ?thesis by blast
	    qed
	    then
	    have "\<forall>a\<in>outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>j.
	      a \<in> read_only (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<longrightarrow> a \<in> read_only \<S>\<^sub>s\<^sub>b"
	      by (auto simp add: in_read_only_convs) 

	    from no_write_to_read_only_memory_read_only_reads_eq [OF nw this]
	    show ?thesis .
	  qed
	qed
      qed

      have tmps_distinct': "tmps_distinct ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_load_tmps is\<^sub>s\<^sub>b'" 
	  by (auto simp add: "is\<^sub>s\<^sub>b" split: instr.splits)
	from load_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b' "is\<^sub>s\<^sub>b")
      next
	from read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_read_tmps []" by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
	from read_tmps_distinct_nth_update [OF i_bound this]
	show "read_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      next
	from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] 
          load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> read_tmps [] = {}"
	  by (clarsimp)
	from load_tmps_read_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_read_tmps_distinct ts\<^sub>s\<^sub>b'"  by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      qed

      have valid_sops': "valid_sops ts\<^sub>s\<^sub>b'"
      proof -
	from valid_store_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	obtain 
	  valid_store_sops': "\<forall>sop\<in>store_sops is\<^sub>s\<^sub>b'. valid_sop sop"
	  by (auto simp add: "is\<^sub>s\<^sub>b" ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')

	from valid_sops_nth_update [OF i_bound  _ valid_store_sops', where sb= "[]" ]
	show ?thesis by (auto simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      qed

      have valid_dd': "valid_data_dependency ts\<^sub>s\<^sub>b'"
      proof -
	from data_dependency_consistent_instrs [OF i_bound ts\<^sub>s\<^sub>b_i]
	obtain 
	  dd_is: "data_dependency_consistent_instrs (dom \<theta>\<^sub>s\<^sub>b')  is\<^sub>s\<^sub>b'"
	  by (auto simp add: "is\<^sub>s\<^sub>b" \<theta>\<^sub>s\<^sub>b')
	from load_tmps_write_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> \<Union>(fst ` write_sops [])  = {}"
	  by (auto simp add: write_sops_append)
	from valid_data_dependency_nth_update [OF i_bound dd_is this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b')
      qed

      have load_tmps_fresh': "load_tmps_fresh ts\<^sub>s\<^sub>b'"
      proof -
	from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "load_tmps (RMW a t (D,f) cond ret A L R W # is\<^sub>s\<^sub>b') \<inter> dom \<theta>\<^sub>s\<^sub>b = {}"
	  by (simp add: "is\<^sub>s\<^sub>b")
	moreover
	from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] have "t \<notin> load_tmps is\<^sub>s\<^sub>b'"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	ultimately have "load_tmps is\<^sub>s\<^sub>b' \<inter> dom (\<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m\<^sub>s\<^sub>b a) (f (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m\<^sub>s\<^sub>b a))))) = {}"
	  by auto
	from load_tmps_fresh_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<theta>\<^sub>s\<^sub>b')
      qed

      from enough_flushs_nth_update [OF i_bound, where sb="[]" ]
      have enough_flushs': "enough_flushs ts\<^sub>s\<^sub>b'"
	by (auto simp: ts\<^sub>s\<^sub>b' sb' sb)


      have valid_program_history': "valid_program_history ts\<^sub>s\<^sub>b'"
      proof -	
	have causal': "causal_program_history is\<^sub>s\<^sub>b' sb'"
	  by (simp add: "is\<^sub>s\<^sub>b" sb sb')
	have "last_prog p\<^sub>s\<^sub>b sb' = p\<^sub>s\<^sub>b"
	  by (simp add: sb' sb)
	from valid_program_history_nth_update [OF i_bound causal' this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      from is_sim have "is": "is = RMW a t (D,f) cond ret A L R W # is\<^sub>s\<^sub>b'"
	by (simp add: suspends sb "is\<^sub>s\<^sub>b")

      from direct_memop_step.RMWWrite [where cond=cond and \<theta>=\<theta>\<^sub>s\<^sub>b and m=m, OF cond']
      have "(RMW a t (D, f) cond ret A L R W # is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (),m, \<D>, \<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b, \<S>) \<rightarrow> 
            (is\<^sub>s\<^sub>b',\<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m a)))), (), 
             m(a := f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a))), False, \<O>\<^sub>s\<^sub>b \<union> A - R, Map.empty, \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

      from direct_computation.concurrent_step.Memop [OF i_bound' ts_i this]
      have "(ts, m, \<S>) \<Rightarrow>\<^sub>d (ts[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b',\<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m a)))), (), False, \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)], 
             m(a := f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a))),\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

      moreover 

      have tmps_commute: "\<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m\<^sub>s\<^sub>b a) (f (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m\<^sub>s\<^sub>b a)))) = 
	(\<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b - {t}))(t \<mapsto> ret (m\<^sub>s\<^sub>b a) (f (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m\<^sub>s\<^sub>b a))))"
	apply (rule ext)
	apply (auto simp add: restrict_map_def domIff)
	done

	 
      from a_unflushed ts\<^sub>s\<^sub>b_i sb
      have a_unflushed':
	"\<forall>j < length ts\<^sub>s\<^sub>b. 
                  (let (_,_,_,sb\<^sub>j,_,_,_) = ts\<^sub>s\<^sub>b!j 
                  in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))"
	by auto

      have all_shared_L: "\<forall>i p is \<O> \<R> \<D> acq \<theta> sb. i < length ts\<^sub>s\<^sub>b \<longrightarrow>
            ts\<^sub>s\<^sub>b ! i = (p, is, \<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
            all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> L = {}"
      proof -
	{
	  fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	  assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  assume x_shared: "x \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	  assume x_L: "x \<in> L"
	  have False
	  proof (cases "i=j")
	    case True with x_shared ts\<^sub>s\<^sub>b_i jth show False by (simp add: sb)
	  next
	    case False
	    show False
	    proof -
	      from all_shared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]
	      have "all_shared sb\<^sub>j \<subseteq> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j".

	      moreover have "all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<subseteq> all_shared sb\<^sub>j"
		using all_shared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
		by auto
	      moreover
	      from A_unacquired_by_others [rule_format, OF _ False] jth j_bound
	      have "A \<inter> all_acquired sb\<^sub>j = {}" by auto
	      moreover

	      from A_unowned_by_others [rule_format, OF _ False] jth j_bound
	      have "A \<inter> \<O>\<^sub>j = {}"
	        by (auto dest: all_shared_acquired_in)

	      ultimately
	      show False
		using L_subset x_L x_shared
		by blast
	    qed
	  qed
	}
	thus ?thesis by blast
      qed

      have all_shared_A: "\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length ts\<^sub>s\<^sub>b \<longrightarrow>
            ts\<^sub>s\<^sub>b ! i = (p, is, \<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
            all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> A = {}"
      proof -
	{
	  fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	  assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  assume x_shared: "x \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	  assume x_A: "x \<in> A"
	  have False
	  proof (cases "i=j")
	    case True with x_shared ts\<^sub>s\<^sub>b_i jth show False by (simp add: sb)
	  next
	    case False
	    show False
	    proof -
	      from all_shared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]
	      have "all_shared sb\<^sub>j \<subseteq> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j".

	      moreover have "all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<subseteq> all_shared sb\<^sub>j"
		using all_shared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
		by auto
	      moreover
	      from A_unacquired_by_others [rule_format, OF _ False] jth j_bound
	      have "A \<inter> all_acquired sb\<^sub>j = {}" by auto
	      moreover

	      from A_unowned_by_others [rule_format, OF _ False] jth j_bound
	      have "A \<inter> \<O>\<^sub>j = {}"
	        by (auto dest: all_shared_acquired_in)


	      ultimately
	      show False
		using x_A x_shared 
		by blast
	    qed
	  qed
	}
	thus ?thesis by blast
      qed
      hence all_shared_L: "\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length ts\<^sub>s\<^sub>b \<longrightarrow>
            ts\<^sub>s\<^sub>b ! i = (p, is, \<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
            all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> L = {}"
	using L_subset by blast

     have all_unshared_R: "\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length ts\<^sub>s\<^sub>b \<longrightarrow>
            ts\<^sub>s\<^sub>b ! i = (p, is, \<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
            all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}"
      proof -
	{
	  fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	  assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  assume x_unshared: "x \<in> all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	  assume x_R: "x \<in> R"
	  have False
	  proof (cases "i=j")
	    case True with x_unshared ts\<^sub>s\<^sub>b_i jth show False by (simp add: sb)
	  next
	    case False
	    show False
	    proof -
	      from unshared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]
	      have "all_unshared sb\<^sub>j \<subseteq> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j".

	      moreover have "all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<subseteq> all_unshared sb\<^sub>j"
		using all_unshared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
		by auto
	      moreover

	      note ownership_distinct [OF i_bound j_bound False ts\<^sub>s\<^sub>b_i jth]

	      ultimately
	      show False
		using  R_owned x_R x_unshared
		by blast
	    qed
	  qed
	}
	thus ?thesis by blast
      qed

     have all_acquired_R: "\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length ts\<^sub>s\<^sub>b \<longrightarrow>
            ts\<^sub>s\<^sub>b ! i = (p, is, \<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
            all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}"
      proof -
	{
	  fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	  assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  assume x_acq: "x \<in> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	  assume x_R: "x \<in> R"
	  have False
	  proof (cases "i=j")
	    case True with x_acq ts\<^sub>s\<^sub>b_i jth show False by (simp add: sb)
	  next
	    case False
	    show False
	    proof -

	      from x_acq have "x \<in> all_acquired sb\<^sub>j"
		using all_acquired_append [of "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j" 
		  "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j"]
		by auto
	      moreover
	      note ownership_distinct [OF i_bound j_bound False ts\<^sub>s\<^sub>b_i jth]
	      ultimately
	      show False
		using  R_owned x_R 
		by blast
	    qed
	  qed
	}
	thus ?thesis by blast
      qed

      have all_shared_R: "\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length ts\<^sub>s\<^sub>b \<longrightarrow>
            ts\<^sub>s\<^sub>b ! i = (p, is, \<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
            all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}"
      proof -
	{
	  fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	  assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  assume x_shared: "x \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	  assume x_R: "x \<in> R"
	  have False
	  proof (cases "i=j")
	    case True with x_shared ts\<^sub>s\<^sub>b_i jth show False by (simp add: sb)
	  next
	    case False
	    show False
	    proof -
	      from all_shared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]
	      have "all_shared sb\<^sub>j \<subseteq> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j".

	      moreover have "all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<subseteq> all_shared sb\<^sub>j"
		using all_shared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
		by auto
	      moreover
	      note ownership_distinct [OF i_bound j_bound False ts\<^sub>s\<^sub>b_i jth]
	      ultimately 
	      show False
		using R_owned x_R x_shared
		by blast
	    qed
	  qed
	}
	thus ?thesis by blast
      qed

      from share_all_until_volatile_write_commute [OF \<open>ownership_distinct ts\<^sub>s\<^sub>b\<close> \<open>sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> 
	all_shared_L all_shared_A all_acquired_R all_unshared_R all_shared_R]
      have share_commute: "share_all_until_volatile_write ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L =
        share_all_until_volatile_write ts\<^sub>s\<^sub>b (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

      {
	fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	assume j_bound: "j < length ts\<^sub>s\<^sub>b"
        assume neq: "i \<noteq> j" 

        have "release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)
                            (dom \<S>\<^sub>s\<^sub>b \<union> R - L) \<R>\<^sub>j
              = release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)
                            (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j"
        proof -
          {
            fix a
            assume a_in: "a \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
            have "(a \<in> (dom \<S>\<^sub>s\<^sub>b \<union> R - L)) = (a \<in> dom \<S>\<^sub>s\<^sub>b)"
            proof -
              from A_unowned_by_others [rule_format, OF j_bound neq ] jth
              A_unacquired_by_others [rule_format, OF _ neq] j_bound
              have A_dist: "A \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {}"
                by (auto dest: all_shared_acquired_in)
              
              from  all_shared_acquired_or_owned [OF sharing_consis [OF j_bound jth]] a_in
              all_shared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
                "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
              have a_in: "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
                by auto
              with ownership_distinct [OF i_bound j_bound neq  ts\<^sub>s\<^sub>b_i jth]
              have "a \<notin> (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb)" by auto

              
              with A_dist R_owned A_R A_shared_owned L_subset a_in
              obtain "a \<notin> R" and "a \<notin> L"
                by fastforce
              then show ?thesis by auto
            qed
          }
          then 
          show ?thesis 
            apply -
            apply (rule release_all_shared_exchange)
            apply auto
            done
        qed
      }
      note release_commute = this
      have "(ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b(a := f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m\<^sub>s\<^sub>b a))),\<S>\<^sub>s\<^sub>b') \<sim> (ts[i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b',
            \<theta>\<^sub>s\<^sub>b(t \<mapsto> ret (m a) (f (\<theta>\<^sub>s\<^sub>b(t\<mapsto>m a)))),(), False,\<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)],m(a := f (\<theta>\<^sub>s\<^sub>b(t \<mapsto> m a))),\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	apply (rule sim_config.intros)
	apply    (simp only: m_a )
	apply    (simp only: m)
	apply    (simp only: flush_all_until_volatile_write_update_other [OF a_unflushed', symmetric] ts\<^sub>s\<^sub>b')
	apply    (simp add: flush_all_until_volatile_nth_update_unused [OF i_bound ts\<^sub>s\<^sub>b_i, simplified sb] sb')
	apply    (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' m 
	  flush_all_until_volatile_nth_update_unused [OF i_bound ts\<^sub>s\<^sub>b_i, simplified sb])
	using  share_all_until_volatile_write_RMW_commute [OF i_bound ts\<^sub>s\<^sub>b_i [simplified is\<^sub>s\<^sub>b sb]]
	apply  (clarsimp simp add: \<S> ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' is\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb' sb share_commute)
	using  leq
	apply  (simp add: ts\<^sub>s\<^sub>b')
	using i_bound i_bound' ts_sim
	apply (clarsimp simp add: Let_def nth_list_update 
	  ts\<^sub>s\<^sub>b' sb' sb \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' \<D>\<^sub>s\<^sub>b'  ex_not m_a  
	  split: if_split_asm)
        apply (rule conjI)
        apply  clarsimp
        apply  (rule tmps_commute)
        apply clarsimp
        apply (frule (2) release_commute)
        apply clarsimp
        apply fastforce
	done
      ultimately 
      show ?thesis
	using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' valid_sops'
	  valid_dd' load_tmps_fresh' enough_flushs' 
	  valid_program_history' valid' m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' 
	by (auto simp del: fun_upd_apply)	
    next
      case (SBHGhost A L R W)
      then obtain 
	"is\<^sub>s\<^sub>b": "is\<^sub>s\<^sub>b = Ghost A L R W# is\<^sub>s\<^sub>b'" and
	\<O>\<^sub>s\<^sub>b': "\<O>\<^sub>s\<^sub>b'=\<O>\<^sub>s\<^sub>b" and
        \<R>\<^sub>s\<^sub>b': "\<R>\<^sub>s\<^sub>b'=\<R>\<^sub>s\<^sub>b" and
	\<theta>\<^sub>s\<^sub>b': "\<theta>\<^sub>s\<^sub>b' = \<theta>\<^sub>s\<^sub>b" and
	\<D>\<^sub>s\<^sub>b': "\<D>\<^sub>s\<^sub>b'=\<D>\<^sub>s\<^sub>b" and
	sb': "sb'=sb@[Ghost\<^sub>s\<^sub>b A L R W]" and
	m\<^sub>s\<^sub>b': "m\<^sub>s\<^sub>b' = m\<^sub>s\<^sub>b" and
	\<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'=\<S>\<^sub>s\<^sub>b" 
	by auto

      from safe_memop_flush_sb [simplified is\<^sub>s\<^sub>b] obtain      
        L_subset: "L \<subseteq> A" and
	A_shared_owned: "A \<subseteq> dom (share ?drop_sb \<S>) \<union> acquired True sb \<O>\<^sub>s\<^sub>b" and
	R_acq: "R \<subseteq> acquired True sb \<O>\<^sub>s\<^sub>b" and
	A_R: "A \<inter> R = {}" and
        A_unowned_by_others_ts:  
	"\<forall>j<length (map owned ts). i\<noteq>j \<longrightarrow> (A \<inter> (owned (ts!j) \<union> dom (released (ts!j))) = {})" 
	by cases auto

      from A_unowned_by_others_ts ts_sim leq
      have A_unowned_by_others:  
	"\<forall>j<length ts\<^sub>s\<^sub>b. i\<noteq>j \<longrightarrow> (let (_,_,_,sb\<^sub>j,_,\<O>\<^sub>j,_) = ts\<^sub>s\<^sub>b!j 
	  in A \<inter> (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j \<union>
                  all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)) = {})" 
  apply (clarsimp simp add: Let_def)
  subgoal for j
	apply (drule_tac x=j in spec)
	apply (force simp add: dom_release_takeWhile)
	done
  done
      have A_unused_by_others:
	  "\<forall>j<length (map \<O>_sb ts\<^sub>s\<^sub>b). i \<noteq> j \<longrightarrow>
             (let (\<O>\<^sub>j, sb\<^sub>j) = map \<O>_sb ts\<^sub>s\<^sub>b! j
             in A \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j = {})"
      proof -
	{
	  fix j \<O>\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length (map owned ts\<^sub>s\<^sub>b)"
	  assume neq_i_j: "i\<noteq>j"
	  assume ts\<^sub>s\<^sub>b_j: "(map \<O>_sb ts\<^sub>s\<^sub>b)!j = (\<O>\<^sub>j,sb\<^sub>j)"
	  assume conflict: "A \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {}"
	  have False
	  proof -
	    from j_bound leq
	    have j_bound': "j < length (map owned ts)"
	      by auto
	    from j_bound have j_bound'': "j < length ts\<^sub>s\<^sub>b"
	      by auto
	    from j_bound' have j_bound''': "j < length ts"
	      by simp
	    
	    from conflict obtain a' where
	      a'_in: "a' \<in> A" and
              a'_in_j: "a' \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
	      by auto

	    let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"

	    from ts_sim [rule_format, OF  j_bound''] ts\<^sub>s\<^sub>b_j j_bound''
	    obtain p\<^sub>j suspends\<^sub>j "is\<^sub>s\<^sub>b\<^sub>j" \<theta>\<^sub>s\<^sub>b\<^sub>j \<D>\<^sub>s\<^sub>b\<^sub>j \<D>\<^sub>j \<R>\<^sub>j "is\<^sub>j" where
	      ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j,\<theta>\<^sub>s\<^sub>b\<^sub>j, sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
	      suspends\<^sub>j: "suspends\<^sub>j = ?drop_sb\<^sub>j" and
	      \<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
	      is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
	      ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
	             \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), 
	             \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j, release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	      apply (cases "ts\<^sub>s\<^sub>b!j")
	      apply (force simp add: Let_def)
	      done
	      
	    have "a' \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b suspends\<^sub>j"
	    proof -	
	      from a'_in_j 
	      have "a' \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (?take_sb\<^sub>j @ ?drop_sb\<^sub>j)"
		by simp
	      thus ?thesis
		apply (simp only: outstanding_refs_append suspends\<^sub>j)
		apply (auto simp add: outstanding_refs_conv dest: set_takeWhileD)
		done
	    qed
		
	    from split_volatile_Write\<^sub>s\<^sub>b_in_outstanding_refs [OF this]
	    obtain sop v ys zs A' L' R' W' where
	      split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a' sop v A' L' R' W' # zs" (is "suspends\<^sub>j = ?suspends")
	      by blast
	    
	    from direct_memop_step.Ghost [where  \<theta>=\<theta>\<^sub>s\<^sub>b and m="flush ?drop_sb m"]
	    have "(Ghost A L R W# is\<^sub>s\<^sub>b', 
                       \<theta>\<^sub>s\<^sub>b, (), flush ?drop_sb m, \<D>\<^sub>s\<^sub>b, 
                       acquired True sb \<O>\<^sub>s\<^sub>b, release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b, share ?drop_sb \<S>) \<rightarrow> 
                    (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), flush ?drop_sb m, \<D>\<^sub>s\<^sub>b, 
                      acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R, 
                      augment_rels (dom (share ?drop_sb \<S>)) R (release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b),
                      share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".
	   
	    from direct_computation.concurrent_step.Memop [OF 
	      i_bound_ts' [simplified is\<^sub>s\<^sub>b] ts'_i [simplified is\<^sub>s\<^sub>b] this [simplified is\<^sub>s\<^sub>b]] 
	    have store_step: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>) \<Rightarrow>\<^sub>d 
                    (?ts'[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (),\<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R,augment_rels (dom (share ?drop_sb \<S>)) R (release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b))], 
                         flush ?drop_sb m,share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		  (is " _ \<Rightarrow>\<^sub>d (?ts_A, ?m_A, ?share_A)")
	     by (simp add: is\<^sub>s\<^sub>b)
	      
	       
	   from i_bound' have i_bound'': "i < length ?ts_A"
	     by simp

	   from valid_program_history [OF j_bound'' ts\<^sub>s\<^sub>b_j] 
	   have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	   then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
	     apply -
	     apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
	     apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	     apply (simp add: split_suspends\<^sub>j)
	     done
	   
	   from ts\<^sub>j neq_i_j j_bound 
	   have ts_A_j: "?ts_A!j = (hd_prog p\<^sub>j (ys @ Write\<^sub>s\<^sub>b True a' sop v A' L' R' W' # zs), is\<^sub>j,
	     \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (ys @ Write\<^sub>s\<^sub>b True a' sop v A' L' R' W' # zs)), (), \<D>\<^sub>j, 
	     acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	     by (simp add: split_suspends\<^sub>j)


	   from j_bound''' i_bound' neq_i_j have j_bound'''': "j < length ?ts_A"
	     by simp

	   from valid_last_prog [OF j_bound'' ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	   then
	   have lp: "last_prog p\<^sub>j ?suspends = p\<^sub>j"
	     apply -
	     apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
	     apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	     apply simp
	     done

	   from valid_reads [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have reads_consis: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".

	   from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> j_bound''
	     ts\<^sub>s\<^sub>b_j reads_consis]
	   have reads_consis_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
	     by (simp add: m suspends\<^sub>j)

	   from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound'' neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j]
	   have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
	     by (simp add: suspends\<^sub>j)
	   from reads_consistent_flush_independent [OF this reads_consis_m]
	   have reads_consis_flush_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
	     ?m_A suspends\<^sub>j".
	   hence reads_consis_m_A_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)  ?m_A ys"
	     by (simp add: split_suspends\<^sub>j reads_consistent_append)


	   from valid_history [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have h_consis: 
	     "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
	     apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	     apply simp
	     done

	   have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	   proof -
	     from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
	       by simp
	     from last_prog_hd_prog_append' [OF h_consis] this
	     have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
	       by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	     moreover 
	     have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		  last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
	       apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	       by (rule last_prog_hd_prog_append)
	     ultimately show ?thesis
	       by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	   qed

	   from valid_write_sops [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
	     by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	   then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
	     valid_sops_drop: "\<forall>sop\<in>write_sops ys. valid_sop sop"
	     apply (simp only: write_sops_append )
	     apply auto
	     done

	   from read_tmps_distinct [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	   have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
	     by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	   then obtain 
	     read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
	     distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
	     apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	     apply (simp only: distinct_read_tmps_append)
	     done
	   
	   from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop h_consis]	  
	     last_prog_hd_prog
	   have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
	     by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	    from reads_consistent_drop_volatile_writes_no_volatile_reads  
	    [OF reads_consis] 
	    have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b ys = {}"
	      by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		split_suspends\<^sub>j )
	   
	    from flush_store_buffer_append [
	      OF j_bound''''  is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
	      ts_A_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_m_A_ys
	      hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
	      no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
	      \<S>="?share_A"]
	    obtain is\<^sub>j' \<R>\<^sub>j' where
	      is\<^sub>j': "instrs (Write\<^sub>s\<^sub>b True a' sop v A' L' R' W' # zs) @ is\<^sub>s\<^sub>b\<^sub>j = 
	            is\<^sub>j' @ prog_instrs (Write\<^sub>s\<^sub>b True a' sop v A' L' R' W' # zs)" and
	      steps_ys: "(?ts_A, ?m_A, ?share_A)  \<Rightarrow>\<^sub>d\<^sup>* 
		(?ts_A[j:= (last_prog (hd_prog p\<^sub>j (Write\<^sub>s\<^sub>b True a' sop v A' L' R' W' # zs)) ys,
                           is\<^sub>j',
                           \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Write\<^sub>s\<^sub>b True a' sop v A' L' R' W' # zs)),(),
                           \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j') ],
                  flush ys ?m_A,
                  share ys ?share_A)"
		 (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
              by (auto)

	    note conflict_computation = rtranclp_trans [OF rtranclp_r_rtranclp [OF steps_flush_sb, OF store_step] steps_ys]
	    from cph
	    have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ((ys @ [Write\<^sub>s\<^sub>b True a' sop v A' L' R' W']) @ zs)"
	      by simp
	    from causal_program_history_suffix [OF this]
	    have cph': "causal_program_history is\<^sub>s\<^sub>b\<^sub>j zs".	      
	    interpret causal\<^sub>j: causal_program_history "is\<^sub>s\<^sub>b\<^sub>j" "zs" by (rule cph')

	    from causal\<^sub>j.causal_program_history [of "[]", simplified, OF refl] is\<^sub>j'   
	    obtain is\<^sub>j''
	      where is\<^sub>j': "is\<^sub>j' = Write True a' sop A' L' R' W' #is\<^sub>j''" and
	      is\<^sub>j'': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j'' @ prog_instrs zs"
	      by clarsimp

	    from j_bound'''
	    have j_bound_ys: "j < length ?ts_ys"
	      by auto

	    from j_bound_ys neq_i_j
	    have ts_ys_j: "?ts_ys!j=(last_prog (hd_prog p\<^sub>j (Write\<^sub>s\<^sub>b True a' sop v A' L' R' W'# zs)) ys, is\<^sub>j',
                 \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Write\<^sub>s\<^sub>b True a' sop v A' L' R' W'# zs)),(),
                 \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {},
                 acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')"
	      by auto

	    from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	    have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	    
	    from safe_delayedE [OF this j_bound_ys ts_ys_j, simplified is\<^sub>j']
	    have a_unowned: 
		"\<forall>i < length ?ts_ys. j\<noteq>i \<longrightarrow> (let (\<O>\<^sub>i) = map owned ?ts_ys!i in a' \<notin> \<O>\<^sub>i)"
	      apply cases
	      apply (auto simp add: Let_def is\<^sub>s\<^sub>b)
	      done
	    from a'_in a_unowned [rule_format, of i] neq_i_j i_bound' A_R
	    show False
	      by (auto simp add: Let_def)
	  qed
	}
	thus ?thesis
	  by (auto simp add: Let_def)
      qed

      have A_unaquired_by_others:
	  "\<forall>j<length (map \<O>_sb ts\<^sub>s\<^sub>b). i \<noteq> j \<longrightarrow>
             (let (\<O>\<^sub>j, sb\<^sub>j) = map \<O>_sb ts\<^sub>s\<^sub>b! j
             in A \<inter> all_acquired sb\<^sub>j = {})"
      proof -
	{
	  fix j \<O>\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length (map owned ts\<^sub>s\<^sub>b)"
	  assume neq_i_j: "i\<noteq>j"
	  assume ts\<^sub>s\<^sub>b_j: "(map \<O>_sb ts\<^sub>s\<^sub>b)!j = (\<O>\<^sub>j,sb\<^sub>j)"
	  assume conflict: "A \<inter> all_acquired sb\<^sub>j \<noteq> {}"
	  have False
	  proof -
	    from j_bound leq
	    have j_bound': "j < length (map owned ts)"
	      by auto
	    from j_bound have j_bound'': "j < length ts\<^sub>s\<^sub>b"
	      by auto
	    from j_bound' have j_bound''': "j < length ts"
	      by simp
	    
	    from conflict obtain a' where
	      a'_in: "a' \<in> A" and
              a'_in_j: "a' \<in> all_acquired sb\<^sub>j"
	      by auto

	    let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"

	    from ts_sim [rule_format, OF  j_bound''] ts\<^sub>s\<^sub>b_j j_bound''
	    obtain p\<^sub>j suspends\<^sub>j "is\<^sub>s\<^sub>b\<^sub>j" \<theta>\<^sub>s\<^sub>b\<^sub>j \<D>\<^sub>s\<^sub>b\<^sub>j \<D>\<^sub>j \<R>\<^sub>j "is\<^sub>j" where
	      ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j, \<theta>\<^sub>s\<^sub>b\<^sub>j, sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
	      suspends\<^sub>j: "suspends\<^sub>j = ?drop_sb\<^sub>j" and
	      \<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
	      is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
	      ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
	                   \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), 
                           \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	      apply (cases "ts\<^sub>s\<^sub>b!j")
	      apply (force simp add: Let_def)
	      done

	    from a'_in_j all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	    have "a' \<in> all_acquired ?take_sb\<^sub>j \<or> a' \<in> all_acquired suspends\<^sub>j"
	      by (auto simp add: suspends\<^sub>j)
	    thus False
	    proof 
	      assume "a' \<in> all_acquired ?take_sb\<^sub>j"
	      with A_unowned_by_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound a'_in
	      show False
		by (auto dest: all_acquired_unshared_acquired)
	    next
	      assume conflict_drop: "a' \<in> all_acquired suspends\<^sub>j"
	      from split_all_acquired_in [OF conflict_drop]
	      (* FIXME: exract common parts *)
	      show False
	      proof 
		assume "\<exists>sop a'' v ys zs A L R W. 
                         suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a'' sop v A L R W# zs \<and> a' \<in> A" 
	        then
		obtain a'' sop' v' ys zs A' L' R' W' where
		  split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs" 
		    (is "suspends\<^sub>j = ?suspends") and
		  a'_A': "a' \<in> A'"
		 by auto
	    
	       from direct_memop_step.Ghost [where  \<theta>=\<theta>\<^sub>s\<^sub>b and m="flush ?drop_sb m"]
	       have "(Ghost A L R W# is\<^sub>s\<^sub>b', 
                         \<theta>\<^sub>s\<^sub>b, (), flush ?drop_sb m,\<D>\<^sub>s\<^sub>b, 
                         acquired True sb \<O>\<^sub>s\<^sub>b, release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b,share ?drop_sb \<S>) \<rightarrow> 
                    (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), flush ?drop_sb m, \<D>\<^sub>s\<^sub>b, 
                      acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R, 
                      augment_rels (dom (share ?drop_sb \<S>)) R (release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b),
                      share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

	       from direct_computation.concurrent_step.Memop [OF 
		 i_bound_ts' [simplified is\<^sub>s\<^sub>b] ts'_i [simplified is\<^sub>s\<^sub>b] this [simplified is\<^sub>s\<^sub>b]] 
	       have store_step: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>) \<Rightarrow>\<^sub>d 
                   (?ts'[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b',\<theta>\<^sub>s\<^sub>b, (),\<D>\<^sub>s\<^sub>b, 
                         acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R,
                         augment_rels (dom (share ?drop_sb \<S>)) R (release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b))], 
          
                         flush ?drop_sb m,share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		   (is " _ \<Rightarrow>\<^sub>d (?ts_A, ?m_A, ?share_A)")
		 by (simp add: is\<^sub>s\<^sub>b)
	      
	       
	       from i_bound' have i_bound'': "i < length ?ts_A"
		 by simp

	       from valid_program_history [OF j_bound'' ts\<^sub>s\<^sub>b_j] 
	       have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	       then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
		 apply -
		 apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		 apply (simp add: split_suspends\<^sub>j)
		 done
	       
	       from ts\<^sub>j neq_i_j j_bound 
	       have ts_A_j: "?ts_A!j = (hd_prog p\<^sub>j (ys @ Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs), is\<^sub>j,
		   \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (ys @ Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs)), (), \<D>\<^sub>j, 
		   acquired True ?take_sb\<^sub>j \<O>\<^sub>j, release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
		 by (simp add: split_suspends\<^sub>j)


	       from j_bound''' i_bound' neq_i_j have j_bound'''': "j < length ?ts_A"
		 by simp

	       from valid_last_prog [OF j_bound'' ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	       then
	       have lp: "last_prog p\<^sub>j ?suspends = p\<^sub>j"
		 apply -
		 apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		 apply simp
		 done
	       

	       from valid_reads [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have reads_consis: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	       
	       from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> j_bound''
		 ts\<^sub>s\<^sub>b_j reads_consis]
	       have reads_consis_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
		 by (simp add: m suspends\<^sub>j)

	       from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound'' neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j]
	       have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
		 by (simp add: suspends\<^sub>j)
	       from reads_consistent_flush_independent [OF this reads_consis_m]
	       have reads_consis_flush_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
		 ?m_A suspends\<^sub>j".
	       hence reads_consis_m_A_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)  ?m_A ys"
		 by (simp add: split_suspends\<^sub>j reads_consistent_append)       
	       
	       from valid_history [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have h_consis: 
		 "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		 apply simp
		 done
	       
	       have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	       proof -
		 from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		   by simp
		 from last_prog_hd_prog_append' [OF h_consis] this
		 have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		   by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		 moreover 
		 have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		   last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		   apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		   by (rule last_prog_hd_prog_append)
		 ultimately show ?thesis
		   by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	       qed
	       
	       from valid_write_sops [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
		 by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	       then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		 valid_sops_drop: "\<forall>sop\<in>write_sops ys. valid_sop sop"
		 apply (simp only: write_sops_append )
		 apply auto
		 done
	       
	       from read_tmps_distinct [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
		 by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	       then obtain 
		 read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
		 distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		 apply (simp only: distinct_read_tmps_append)
		 done
	       
	       from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop h_consis]	  
		 last_prog_hd_prog
	       have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
		 by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	       from reads_consistent_drop_volatile_writes_no_volatile_reads  
	       [OF reads_consis] 
	       have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b ys = {}"
		 by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		   split_suspends\<^sub>j )
	       
	       from flush_store_buffer_append [
		 OF j_bound''''  is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
		 ts_A_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_m_A_ys
		 hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
		 no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
		 \<S>="?share_A"]
	       obtain is\<^sub>j' \<R>\<^sub>j' where
		 is\<^sub>j': "instrs (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs) @ is\<^sub>s\<^sub>b\<^sub>j = 
	            is\<^sub>j' @ prog_instrs (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs)" and
		 steps_ys: "(?ts_A, ?m_A, ?share_A)  \<Rightarrow>\<^sub>d\<^sup>* 
		(?ts_A[j:= (last_prog (hd_prog p\<^sub>j (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs)) ys,
                           is\<^sub>j',
                           \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W' # zs)),(),
                           \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j') ],
                  flush ys ?m_A,share ys ?share_A)"
		 (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
		 by (auto)

	       note conflict_computation = rtranclp_trans [OF rtranclp_r_rtranclp [OF steps_flush_sb, OF store_step] steps_ys]
	       from cph
	       have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ((ys @ [Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W']) @ zs)"
		 by simp
	       from causal_program_history_suffix [OF this]
	       have cph': "causal_program_history is\<^sub>s\<^sub>b\<^sub>j zs".	      
	       interpret causal\<^sub>j: causal_program_history "is\<^sub>s\<^sub>b\<^sub>j" "zs" by (rule cph')

	       from causal\<^sub>j.causal_program_history [of "[]", simplified, OF refl] is\<^sub>j'   
	       obtain is\<^sub>j''
		 where is\<^sub>j': "is\<^sub>j' = Write True a'' sop' A' L' R' W'#is\<^sub>j''" and
		 is\<^sub>j'': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j'' @ prog_instrs zs"
		 by clarsimp
	       
	       from j_bound'''
	       have j_bound_ys: "j < length ?ts_ys"
		 by auto

	       from j_bound_ys neq_i_j
	       have ts_ys_j: "?ts_ys!j=(last_prog (hd_prog p\<^sub>j (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W'# zs)) ys, is\<^sub>j',
                 \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W'# zs)),(), 
		 \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {},
                 acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')"
		 by auto

	       from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	       have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	    
	       from safe_delayedE [OF this j_bound_ys ts_ys_j, simplified is\<^sub>j']
	       have A'_unowned: 
		 "\<forall>i < length ?ts_ys. j\<noteq>i \<longrightarrow> (let (\<O>\<^sub>i) = map owned ?ts_ys!i in A' \<inter>  \<O>\<^sub>i = {})"
		 apply cases
		 apply (fastforce simp add: Let_def is\<^sub>s\<^sub>b)+
		 done
	       from a'_in a'_A' A'_unowned [rule_format, of i] neq_i_j i_bound' A_R 
	       show False
		 by (auto simp add: Let_def)
	     next
	       assume "\<exists>A L R W ys zs. 
                 suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A L R W # zs \<and> a' \<in> A" 
	       then
	       obtain ys zs A' L' R' W' where
		  split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs" (is "suspends\<^sub>j = ?suspends") and
		 a'_A': "a' \<in> A'"
		 by auto
		 
	       from direct_memop_step.Ghost [where  \<theta>=\<theta>\<^sub>s\<^sub>b and m="flush ?drop_sb m"]
	       have "(Ghost A L R W# is\<^sub>s\<^sub>b', 
                       \<theta>\<^sub>s\<^sub>b, (), flush ?drop_sb m, \<D>\<^sub>s\<^sub>b, 
                       acquired True sb \<O>\<^sub>s\<^sub>b, release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b, share ?drop_sb \<S>) \<rightarrow> 
                    (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), flush ?drop_sb m, \<D>\<^sub>s\<^sub>b, 
                      acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R, 
                      augment_rels (dom (share ?drop_sb \<S>)) R (release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b),
                      share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

	       from direct_computation.concurrent_step.Memop [OF 
		 i_bound_ts' [simplified is\<^sub>s\<^sub>b] ts'_i [simplified is\<^sub>s\<^sub>b] this [simplified is\<^sub>s\<^sub>b]] 
	       have store_step: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>) \<Rightarrow>\<^sub>d 
                   (?ts'[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), \<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R,augment_rels (dom (share ?drop_sb \<S>)) R (release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b))], 
                         flush ?drop_sb m,share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		   (is " _ \<Rightarrow>\<^sub>d (?ts_A, ?m_A, ?share_A)")
		 by (simp add: is\<^sub>s\<^sub>b)
	      
	       
	       from i_bound' have i_bound'': "i < length ?ts_A"
		 by simp

	       from valid_program_history [OF j_bound'' ts\<^sub>s\<^sub>b_j] 
	       have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	       then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
		 apply -
		 apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		 apply (simp add: split_suspends\<^sub>j)
		 done
	       
	       from ts\<^sub>j neq_i_j j_bound 
	       have ts_A_j: "?ts_A!j = (hd_prog p\<^sub>j (ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs), is\<^sub>j,
		 \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)), (),\<D>\<^sub>j, 
		 acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
		 by (simp add: split_suspends\<^sub>j)


	       from j_bound''' i_bound' neq_i_j have j_bound'''': "j < length ?ts_A"
		 by simp
	       
	       from valid_last_prog [OF j_bound'' ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	       then
	       have lp: "last_prog p\<^sub>j ?suspends = p\<^sub>j"
		 apply -
		 apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		 apply simp
		 done
	       from valid_reads [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have reads_consis: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	       
	       from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> j_bound''
		 ts\<^sub>s\<^sub>b_j reads_consis]
	       have reads_consis_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
		 by (simp add: m suspends\<^sub>j)

	       from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound'' neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j]
	       have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
		 by (simp add: suspends\<^sub>j)
	       from reads_consistent_flush_independent [OF this reads_consis_m]
	       have reads_consis_flush_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
		 ?m_A suspends\<^sub>j".
	       hence reads_consis_m_A_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)  ?m_A ys"
		 by (simp add: split_suspends\<^sub>j reads_consistent_append)


	       from valid_history [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have h_consis: 
		 "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		 apply simp
		 done
	       
	       have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	       proof -
		 from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		   by simp
		 from last_prog_hd_prog_append' [OF h_consis] this
		 have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		   by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		 moreover 
		 have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		   last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		   apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		   by (rule last_prog_hd_prog_append)
		 ultimately show ?thesis
		   by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	       qed
	       
	       from valid_write_sops [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
		 by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	       then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		   valid_sops_drop: "\<forall>sop\<in>write_sops ys. valid_sop sop"
		 apply (simp only: write_sops_append )
		 apply auto
		 done
	       
	       from read_tmps_distinct [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	       have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
		 by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	       then obtain 
		 read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
		 distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
		 apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		 apply (simp only: distinct_read_tmps_append)
		 done
	       
	       from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop h_consis]	  
		 last_prog_hd_prog
	       have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
		 by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	       from reads_consistent_drop_volatile_writes_no_volatile_reads  
	       [OF reads_consis] 
	       have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b ys = {}"
		 by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		   split_suspends\<^sub>j )
	   
	       from flush_store_buffer_append [
		 OF j_bound''''  is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
		 ts_A_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_m_A_ys
		 hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
		 no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
		 \<S>="?share_A"]
	       obtain is\<^sub>j' \<R>\<^sub>j' where
		 is\<^sub>j': "instrs (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs) @ is\<^sub>s\<^sub>b\<^sub>j = 
	            is\<^sub>j' @ prog_instrs (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)" and
		 steps_ys: "(?ts_A, ?m_A, ?share_A)  \<Rightarrow>\<^sub>d\<^sup>* 
		(?ts_A[j:= (last_prog (hd_prog p\<^sub>j (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)) ys,
                           is\<^sub>j',
                           \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)),(),
		           \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j') ],
                  flush ys ?m_A,                  share ys ?share_A)"
		 (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
		 by (auto)

	       note conflict_computation = rtranclp_trans [OF rtranclp_r_rtranclp [OF steps_flush_sb, OF store_step] steps_ys]
	       from cph
	       have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ((ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W']) @ zs)"
		 by simp
	       from causal_program_history_suffix [OF this]
	       have cph': "causal_program_history is\<^sub>s\<^sub>b\<^sub>j zs".	      
	       interpret causal\<^sub>j: causal_program_history "is\<^sub>s\<^sub>b\<^sub>j" "zs" by (rule cph')

	       from causal\<^sub>j.causal_program_history [of "[]", simplified, OF refl] is\<^sub>j'   
	       obtain is\<^sub>j''
		 where is\<^sub>j': "is\<^sub>j' = Ghost A' L' R' W'#is\<^sub>j''" and
		 is\<^sub>j'': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j'' @ prog_instrs zs"
		 by clarsimp
	       
	       from j_bound'''
	       have j_bound_ys: "j < length ?ts_ys"
		 by auto

	       from j_bound_ys neq_i_j
	       have ts_ys_j: "?ts_ys!j=(last_prog (hd_prog p\<^sub>j (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)) ys, is\<^sub>j',
                 \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Write\<^sub>s\<^sub>b True a'' sop' v' A' L' R' W'# zs)),(),
		 \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {},
                 acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')"
		 by auto

	       from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	       have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	    
	       from safe_delayedE [OF this j_bound_ys ts_ys_j, simplified is\<^sub>j']
	       have A'_unowned: 
		 "\<forall>i < length ?ts_ys. j\<noteq>i \<longrightarrow> (let (\<O>\<^sub>i) = map owned ?ts_ys!i in A' \<inter>  \<O>\<^sub>i = {})"
		 apply cases
		 apply (fastforce simp add: Let_def is\<^sub>s\<^sub>b)+
		 done
	       from a'_in a'_A' A'_unowned [rule_format, of i] neq_i_j i_bound' A_R 
	       show False
		 by (auto simp add: Let_def)
	     qed
	   qed
	 qed
       }
       thus ?thesis
	 by (auto simp add: Let_def)
      qed

      have A_no_read_only_reads_by_others:
	  "\<forall>j<length (map \<O>_sb ts\<^sub>s\<^sub>b). i \<noteq> j \<longrightarrow>
             (let (\<O>\<^sub>j, sb\<^sub>j) = map \<O>_sb ts\<^sub>s\<^sub>b! j
             in A \<inter> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j)
	             (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) = {})"
      proof -
	{
	  fix j \<O>\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length (map owned ts\<^sub>s\<^sub>b)"
	  assume neq_i_j: "i\<noteq>j"
	  assume ts\<^sub>s\<^sub>b_j: "(map \<O>_sb ts\<^sub>s\<^sub>b)!j = (\<O>\<^sub>j,sb\<^sub>j)"
	  let ?take_sb\<^sub>j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	  let ?drop_sb\<^sub>j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"

	  assume conflict: "A \<inter> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j  \<noteq> {}"
	  have False
	  proof -
	    from j_bound leq
	    have j_bound': "j < length (map owned ts)"
	      by auto
	    from j_bound have j_bound'': "j < length ts\<^sub>s\<^sub>b"
	      by auto
	    from j_bound' have j_bound''': "j < length ts"
	      by simp
	    
	    from conflict obtain a' where
	      a'_in: "a' \<in> A" and
              a'_in_j: "a' \<in> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
	      by auto


	    from ts_sim [rule_format, OF  j_bound''] ts\<^sub>s\<^sub>b_j j_bound''
	    obtain p\<^sub>j suspends\<^sub>j "is\<^sub>s\<^sub>b\<^sub>j" \<D>\<^sub>s\<^sub>b\<^sub>j \<D>\<^sub>j \<R>\<^sub>j \<theta>\<^sub>s\<^sub>b\<^sub>j "is\<^sub>j" where
	      ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j, \<theta>\<^sub>s\<^sub>b\<^sub>j, sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
	      suspends\<^sub>j: "suspends\<^sub>j = ?drop_sb\<^sub>j" and
	      is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
	      \<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
	      ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j,
	             \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps suspends\<^sub>j),(), \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	      apply (cases "ts\<^sub>s\<^sub>b!j")
	      apply (force simp add: Let_def)
	      done
	      

	    from split_in_read_only_reads [OF a'_in_j [simplified suspends\<^sub>j [symmetric]]]
	    obtain t v ys zs where
	      split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Read\<^sub>s\<^sub>b False a' t v# zs" (is "suspends\<^sub>j = ?suspends") and
	      a'_unacq: "a' \<notin> acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)"
	      by blast

	    
	    from direct_memop_step.Ghost [where  \<theta>=\<theta>\<^sub>s\<^sub>b and m="flush ?drop_sb m"]
	    have "(Ghost A L R W# is\<^sub>s\<^sub>b', 
                       \<theta>\<^sub>s\<^sub>b, (), flush ?drop_sb m, \<D>\<^sub>s\<^sub>b, 
                       acquired True sb \<O>\<^sub>s\<^sub>b, release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b, share ?drop_sb \<S>) \<rightarrow> 
                    (is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (), flush ?drop_sb m, \<D>\<^sub>s\<^sub>b, 
                      acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R, 
                      augment_rels (dom (share ?drop_sb \<S>)) R (release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b),
                      share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

	    from direct_computation.concurrent_step.Memop [OF 
		 i_bound_ts' [simplified is\<^sub>s\<^sub>b] ts'_i [simplified is\<^sub>s\<^sub>b] this [simplified is\<^sub>s\<^sub>b]] 
	    have store_step: "(?ts', flush ?drop_sb m, share ?drop_sb \<S>) \<Rightarrow>\<^sub>d 
                    (?ts'[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', \<theta>\<^sub>s\<^sub>b, (),\<D>\<^sub>s\<^sub>b, acquired True sb \<O>\<^sub>s\<^sub>b \<union> A - R,augment_rels (dom (share ?drop_sb \<S>)) R (release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b))], 
                         flush ?drop_sb m,share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		  (is " _ \<Rightarrow>\<^sub>d (?ts_A, ?m_A, ?share_A)")
	     by (simp add: is\<^sub>s\<^sub>b)
	    
	    from i_bound' have i_bound'': "i < length ?ts_A"
	      by simp

	    from valid_program_history [OF j_bound'' ts\<^sub>s\<^sub>b_j] 
	    have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	    then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
	      apply -
	      apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply (simp add: split_suspends\<^sub>j)
	      done
	       
	    from ts\<^sub>j neq_i_j j_bound 
	    have ts_A_j: "?ts_A!j = (hd_prog p\<^sub>j (ys @ Read\<^sub>s\<^sub>b False a' t v# zs), is\<^sub>j,
	      \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (ys @ Read\<^sub>s\<^sub>b False a' t v# zs)), (),\<D>\<^sub>j, 
	      acquired True ?take_sb\<^sub>j \<O>\<^sub>j,release ?take_sb\<^sub>j (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j)"
	      by (simp add: split_suspends\<^sub>j)
	    

	    from j_bound''' i_bound' neq_i_j have j_bound'''': "j < length ?ts_A"
	      by simp
	       
	    from valid_last_prog [OF j_bound'' ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	    then
	    have lp: "last_prog p\<^sub>j ?suspends = p\<^sub>j"
	      apply -
	      apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done
	    from valid_reads [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	    have reads_consis: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	    
	    from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> j_bound''
		 ts\<^sub>s\<^sub>b_j reads_consis]
	    have reads_consis_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
	      by (simp add: m suspends\<^sub>j)
	    
	    from outstanding_non_write_non_vol_reads_drop_disj [OF i_bound j_bound'' neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j]
	    have "outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b suspends\<^sub>j = {}"
	      by (simp add: suspends\<^sub>j)
	    from reads_consistent_flush_independent [OF this reads_consis_m]
	    have reads_consis_flush_m: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) 
	      ?m_A suspends\<^sub>j".
	    hence reads_consis_m_A_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)  ?m_A ys"
	      by (simp add: split_suspends\<^sub>j reads_consistent_append)
	    

	    from valid_history [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	    have h_consis: 
	      "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      apply simp
	      done
	       
	    have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	    proof -
	      from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		by simp
	      from last_prog_hd_prog_append' [OF h_consis] this
	      have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      moreover 
	      have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		by (rule last_prog_hd_prog_append)
	      ultimately show ?thesis
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	    qed
	    
	    from valid_write_sops [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	    have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		   valid_sops_drop: "\<forall>sop\<in>write_sops ys. valid_sop sop"
	      apply (simp only: write_sops_append )
	      apply auto
	      done
	    
	    from read_tmps_distinct [OF j_bound'' ts\<^sub>s\<^sub>b_j]
	    have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	    then obtain 
		 read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
	      distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
	      apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      apply (simp only: distinct_read_tmps_append)
	      done
	       
	    from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop h_consis]	  
	      last_prog_hd_prog
	    have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
	      by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	    from reads_consistent_drop_volatile_writes_no_volatile_reads  
	    [OF reads_consis] 
	    have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b ys = {}"
	      by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		split_suspends\<^sub>j )
	   
	    from flush_store_buffer_append [
		 OF j_bound''''  is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
		 ts_A_j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_m_A_ys
		 hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
		 no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
		 \<S>="?share_A"]
	    obtain is\<^sub>j' \<R>\<^sub>j' where
		 is\<^sub>j': "instrs (Read\<^sub>s\<^sub>b False a' t v # zs) @ is\<^sub>s\<^sub>b\<^sub>j = 
	            is\<^sub>j' @ prog_instrs (Read\<^sub>s\<^sub>b False a' t v # zs)" and
		 steps_ys: "(?ts_A, ?m_A, ?share_A)  \<Rightarrow>\<^sub>d\<^sup>* 
		(?ts_A[j:= (last_prog (hd_prog p\<^sub>j (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs)) ys,
                           is\<^sub>j',
                           \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Read\<^sub>s\<^sub>b False a' t v # zs)),(),
		           \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j') ],
                  flush ys ?m_A,
                  share ys ?share_A)"
	      (is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
	      by (auto)
	    
	    note conflict_computation = rtranclp_trans [OF rtranclp_r_rtranclp [OF steps_flush_sb, OF store_step] steps_ys]

	    from cph
	    have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ((ys @ [Read\<^sub>s\<^sub>b False a' t v]) @ zs)"
	      by simp
	    from causal_program_history_suffix [OF this]
	    have cph': "causal_program_history is\<^sub>s\<^sub>b\<^sub>j zs".	      
	    interpret causal\<^sub>j: causal_program_history "is\<^sub>s\<^sub>b\<^sub>j" "zs" by (rule cph')

	    from causal\<^sub>j.causal_program_history [of "[]", simplified, OF refl] is\<^sub>j'   
	    obtain is\<^sub>j''
	      where is\<^sub>j': "is\<^sub>j' = Read False a' t#is\<^sub>j''" and
	      is\<^sub>j'': "instrs zs @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j'' @ prog_instrs zs"
	      by clarsimp

	    from j_bound'''
	    have j_bound_ys: "j < length ?ts_ys"
	      by auto

	    from j_bound_ys neq_i_j
	    have ts_ys_j: "?ts_ys!j=(last_prog (hd_prog p\<^sub>j (Read\<^sub>s\<^sub>b False a' t v# zs)) ys, is\<^sub>j',
                 \<theta>\<^sub>s\<^sub>b\<^sub>j |` (dom \<theta>\<^sub>s\<^sub>b\<^sub>j - read_tmps (Read\<^sub>s\<^sub>b False a' t v# zs)),(),
	         \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {},
                 acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j),\<R>\<^sub>j')"
	      by auto

	    from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	    have "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	    
	    from safe_delayedE [OF this j_bound_ys ts_ys_j, simplified is\<^sub>j']
	    have "a' \<in> acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<or>
                  a' \<in> read_only (share ys (share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R  \<ominus>\<^bsub>A\<^esub> L))"
	      apply cases
	      apply (auto simp add: Let_def is\<^sub>s\<^sub>b)
	      done
	    with a'_unacq
	    have a'_ro: "a' \<in> read_only (share ys (share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
	      by auto
	    from a'_in
	    have a'_not_ro: "a' \<notin> read_only (share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R  \<ominus>\<^bsub>A\<^esub> L)"
	      by (auto simp add:  in_read_only_convs)

	    have "a' \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	    proof -
	      {
		assume a_notin: "a' \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
		from weak_sharing_consis [OF j_bound'' ts\<^sub>s\<^sub>b_j]
		have "weak_sharing_consistent \<O>\<^sub>j sb\<^sub>j".
		with weak_sharing_consistent_append [of \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		have "weak_sharing_consistent (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) suspends\<^sub>j"
		  by (auto simp add: suspends\<^sub>j)
		with split_suspends\<^sub>j
		have weak_consis: "weak_sharing_consistent (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ys"
		  by (simp add: weak_sharing_consistent_append)
		from all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		have "all_acquired ys \<subseteq> all_acquired sb\<^sub>j"
		  apply (clarsimp)
		  apply (clarsimp simp add: suspends\<^sub>j [symmetric] split_suspends\<^sub>j all_acquired_append)
		  done
		with a_notin acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b [of sb\<^sub>j \<O>\<^sub>j]
                  all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
		have "a' \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j \<union> all_acquired ys"
                  by auto
                
		from read_only_share_unowned [OF weak_consis this a'_ro] 
		have "a' \<in> read_only (share ?drop_sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" .
		  
		with a'_not_ro have False
		  by auto
	      }
	      thus ?thesis by blast
	    qed
		
	    moreover
	    from A_unaquired_by_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
	    have "A \<inter> all_acquired sb\<^sub>j = {}"
	      by (auto simp add: Let_def)
	    moreover
	    from A_unowned_by_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
	    have "A \<inter> \<O>\<^sub>j = {}"
	      by (auto simp add: Let_def dest: all_shared_acquired_in)
	    moreover note a'_in
	    ultimately
	    show False
	      by auto
	  qed
	}
	thus ?thesis
	  by (auto simp add: Let_def)
      qed

      have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof -
	  from outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i] 
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb @ [Ghost\<^sub>s\<^sub>b A L R W]) "
	    by (auto simp add: non_volatile_owned_or_read_only_append)
	  from outstanding_non_volatile_refs_owned_or_read_only_nth_update [OF i_bound this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	qed
      next
	show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)
	  fix i\<^sub>1 j p\<^sub>1 "is\<^sub>1" \<O>\<^sub>1 \<R>\<^sub>1 \<D>\<^sub>1 xs\<^sub>1 sb\<^sub>1 p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume i\<^sub>1_bound: "i\<^sub>1 < length ts\<^sub>s\<^sub>b'"
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume i\<^sub>1_j: "i\<^sub>1 \<noteq> j"
	  assume ts_i\<^sub>1: "ts\<^sub>s\<^sub>b'!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	  assume ts_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}"
	  proof (cases "i\<^sub>1=i")
	    case True
	    with i\<^sub>1_j have i_j: "i\<noteq>j" 
	      by simp
	    
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    hence j_bound'': "j < length (map owned ts\<^sub>s\<^sub>b)"
	      by simp
	    from ts_j i_j have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (simp add: ts\<^sub>s\<^sub>b')

	    from outstanding_volatile_writes_unowned_by_others 
	    [OF i_bound j_bound' i_j ts\<^sub>s\<^sub>b_i ts_j']
	    have "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}".
	    with ts_i\<^sub>1 True i_bound show ?thesis
	      by (clarsimp simp add: ts\<^sub>s\<^sub>b' sb' outstanding_refs_append 
		acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)
	  next
	    case False
	    note i\<^sub>1_i = this
	    from i\<^sub>1_bound have i\<^sub>1_bound': "i\<^sub>1 < length ts\<^sub>s\<^sub>b"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    from ts_i\<^sub>1 False have ts_i\<^sub>1': "ts\<^sub>s\<^sub>b!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    show ?thesis
	    proof (cases "j=i")
	      case True

	      from i\<^sub>1_bound'
	      have i\<^sub>1_bound'': "i\<^sub>1 < length (map owned ts\<^sub>s\<^sub>b)"
		by simp

	      from outstanding_volatile_writes_unowned_by_others 
	      [OF i\<^sub>1_bound' i_bound i\<^sub>1_i ts_i\<^sub>1' ts\<^sub>s\<^sub>b_i]
	      have "(\<O>\<^sub>s\<^sub>b \<union> all_acquired sb) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}".
	      moreover
	      from A_unused_by_others [rule_format, OF _ False [symmetric]] False ts_i\<^sub>1 i\<^sub>1_bound
	      have "A \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}"
		by (auto simp add: Let_def ts\<^sub>s\<^sub>b')
	      
	      ultimately
	      show ?thesis
		using ts_j True ts\<^sub>s\<^sub>b' 
		by (auto simp add: i_bound ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' all_acquired_append)
	    next
	      case False
	      from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from ts_j False have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from outstanding_volatile_writes_unowned_by_others 
              [OF i\<^sub>1_bound' j_bound' i\<^sub>1_j ts_i\<^sub>1' ts_j']
	      show "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}" .
	    qed
	  qed
	qed
      next
	show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
	proof 
	  fix n m
	  fix p\<^sub>n "is\<^sub>n" \<O>\<^sub>n \<R>\<^sub>n \<D>\<^sub>n \<theta>\<^sub>n sb\<^sub>n p\<^sub>m "is\<^sub>m" \<O>\<^sub>m \<R>\<^sub>m \<D>\<^sub>m \<theta>\<^sub>m sb\<^sub>m
	  assume n_bound: "n < length ts\<^sub>s\<^sub>b'"
	    and m_bound: "m < length ts\<^sub>s\<^sub>b'"
	    and neq_n_m: "n\<noteq>m"
	    and nth: "ts\<^sub>s\<^sub>b'!n = (p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
	    and mth: "ts\<^sub>s\<^sub>b'!m =(p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m,\<R>\<^sub>m)"
	  from n_bound have n_bound': "n < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')
	  from m_bound have m_bound': "m < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')
	  show "(\<O>\<^sub>m \<union> all_acquired sb\<^sub>m) \<inter>
            read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) \<O>\<^sub>n)
            (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) =
            {}"
	  proof (cases "m=i")
	    case True
	    with neq_n_m have neq_n_i: "n\<noteq>i"
	      by auto
	    with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    note read_only_reads_unowned [OF n_bound' i_bound  neq_n_i nth' ts\<^sub>s\<^sub>b_i]
	    moreover
	    from A_no_read_only_reads_by_others [rule_format, OF _ neq_n_i [symmetric]] n_bound' nth'
	    have "A \<inter> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) \<O>\<^sub>n)
              (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) =
              {}"
	      by auto
	    ultimately 
	    show ?thesis
	      using True ts\<^sub>s\<^sub>b_i nth' mth n_bound' m_bound'
	      by (auto simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' all_acquired_append)
	  next
	    case False
	    note neq_m_i = this
	    with m_bound mth i_bound have mth': "ts\<^sub>s\<^sub>b!m = (p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m,\<R>\<^sub>m)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    show ?thesis
	    proof (cases "n=i")
	      case True
	      note read_only_reads_unowned [OF i_bound m_bound' neq_m_i [symmetric] ts\<^sub>s\<^sub>b_i mth']
	      then show ?thesis
		using True neq_m_i ts\<^sub>s\<^sub>b_i nth mth n_bound' m_bound'
		apply (case_tac "outstanding_refs (is_volatile_Write\<^sub>s\<^sub>b) sb = {}")
		apply (clarsimp simp add: outstanding_vol_write_take_drop_appends
		  acquired_append read_only_reads_append ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b')+
		done
	    next
	      case False
	      with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      from read_only_reads_unowned [OF n_bound' m_bound' neq_n_m  nth' mth'] False neq_m_i
	      show ?thesis 
		by (clarsimp)
	    qed
	  qed
	qed
      next
	show "ownership_distinct ts\<^sub>s\<^sub>b'"
	proof -
	  have "\<forall>j<length ts\<^sub>s\<^sub>b. i \<noteq> j \<longrightarrow>
	    (let (p\<^sub>j, is\<^sub>j,\<theta>\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j,\<R>\<^sub>j) = ts\<^sub>s\<^sub>b ! j
	      in (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb') \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {})"
	  proof -
	    {
	      fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j
	      assume neq_i_j: "i \<noteq> j"
	      assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	      assume ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j, is\<^sub>j, \<theta>\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j,\<R>\<^sub>j)"
	      have "(\<O>\<^sub>s\<^sub>b \<union> all_acquired sb') \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {}"
	      proof -
		{
		  fix a'
		  assume a'_in_i: "a' \<in> (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb')"
		  assume a'_in_j: "a' \<in> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j)"
		  have False
		  proof -
		    from a'_in_i have "a' \<in> (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb) \<or> a' \<in> A"
		      by (simp add: sb' all_acquired_append)
		    then show False
		    proof 
		      assume "a' \<in> (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb)"
		      with ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j] a'_in_j
		      show ?thesis
			by auto
		    next
		      assume "a' \<in> A"
		      moreover
		      have j_bound': "j < length (map owned ts\<^sub>s\<^sub>b)"
			using j_bound by auto
		      from A_unowned_by_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
		      obtain "A \<inter> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j = {}" and
                             "A \<inter> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) = {}"
			by (auto simp add: Let_def)
		      moreover
		      from A_unaquired_by_others [rule_format, OF _ neq_i_j] ts\<^sub>s\<^sub>b_j j_bound
		      have "A \<inter> all_acquired sb\<^sub>j = {}"
			by auto
		      ultimately
		      show ?thesis
			using a'_in_j
			by (auto dest: all_shared_acquired_in)
		    qed
		  qed
		}
		then show ?thesis by auto
	      qed
	    }
	    then show ?thesis by (fastforce simp add: Let_def)
	  qed
	
	  from ownership_distinct_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb')
	qed
      qed

      have valid_hist': "valid_history program_step ts\<^sub>s\<^sub>b'"
      proof -
	from valid_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b sb) sb".
	with valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i] 
	  valid_implies_valid_prog_hd [OF i_bound ts\<^sub>s\<^sub>b_i valid]
	have "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b (sb@[Ghost\<^sub>s\<^sub>b A L R W])) 
	         (sb@ [Ghost\<^sub>s\<^sub>b A L R W])"
	  apply -
	  apply (rule history_consistent_appendI)
	  apply (auto simp add: hd_prog_append_Ghost\<^sub>s\<^sub>b)
	  done
	from valid_history_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<theta>\<^sub>s\<^sub>b')
      qed

      have valid_reads': "valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b'"
      proof -
	from valid_reads [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b sb" .
	from reads_consistent_snoc_Ghost\<^sub>s\<^sub>b [OF this]
	have "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b (sb @ [Ghost\<^sub>s\<^sub>b A L R W])".
	from valid_reads_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b') 
      qed

      have valid_sharing': "valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)	
	from outstanding_non_volatile_writes_unshared [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b (sb @ [Ghost\<^sub>s\<^sub>b A L R W])"
	  by (auto simp add: non_volatile_writes_unshared_append)
	from outstanding_non_volatile_writes_unshared_nth_update [OF i_bound this]
	show "outstanding_non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' sb' \<S>\<^sub>s\<^sub>b')
      next
	from sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]
	have consis': "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb".
	from  A_shared_owned
	have "A \<subseteq> dom (share ?drop_sb \<S>) \<union> acquired True sb \<O>\<^sub>s\<^sub>b"
	  by (simp add:  sharing_consistent_append  acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)
	moreover have "dom (share ?drop_sb \<S>) \<subseteq> dom \<S> \<union> dom (share sb \<S>\<^sub>s\<^sub>b)"
	proof
	  fix a'
	  assume a'_in: "a' \<in> dom (share ?drop_sb \<S>)" 
	  from share_unshared_in [OF a'_in]
	  show "a' \<in> dom \<S> \<union> dom (share sb \<S>\<^sub>s\<^sub>b)"
	  proof 
	    assume "a' \<in> dom (share ?drop_sb Map.empty)" 
	    from share_mono_in [OF this] share_append [of ?take_sb ?drop_sb]
	    have "a' \<in> dom (share sb \<S>\<^sub>s\<^sub>b)"
	      by auto
	    thus ?thesis
	      by simp
	  next
	    assume "a' \<in> dom \<S> \<and> a' \<notin> all_unshared ?drop_sb"
	    thus ?thesis by auto
	  qed
	qed
	ultimately
	have A_subset: "A \<subseteq> dom \<S> \<union> dom (share sb \<S>\<^sub>s\<^sub>b) \<union> acquired True sb \<O>\<^sub>s\<^sub>b"
	  by auto
        have "A \<subseteq> dom (share sb \<S>\<^sub>s\<^sub>b) \<union> acquired True sb \<O>\<^sub>s\<^sub>b"
        proof -
          {
            fix x
            assume x_A: "x \<in> A"
            have "x \<in> dom (share sb \<S>\<^sub>s\<^sub>b) \<union> acquired True sb \<O>\<^sub>s\<^sub>b"
            proof -
              {
                assume "x \<in> dom \<S>"
                
                from share_all_until_volatile_write_share_acquired [OF \<open>sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> 
                  i_bound ts\<^sub>s\<^sub>b_i this [simplified \<S>]]
                  A_unowned_by_others x_A
                have ?thesis
                by (fastforce simp add: Let_def)
             }
             with A_subset show ?thesis using x_A by auto
           qed
         }
         thus ?thesis by blast
        qed
	with consis' L_subset A_R R_acq
	have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb @ [Ghost\<^sub>s\<^sub>b A L R W])"
	  by (simp add:  sharing_consistent_append  acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)
	from sharing_consis_nth_update [OF i_bound this]
	show "sharing_consis \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' \<S>\<^sub>s\<^sub>b')

      next
	from read_only_unowned_nth_update [OF i_bound read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] ]
	show "read_only_unowned \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b')
      next
	from unowned_shared_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i subset_refl]
	show "unowned_shared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next
	from no_outstanding_write_to_read_only_memory [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b (sb @ [Ghost\<^sub>s\<^sub>b A L R W])"
	  by (simp add: no_write_to_read_only_memory_append)

	from no_outstanding_write_to_read_only_memory_nth_update [OF i_bound this]
	show "no_outstanding_write_to_read_only_memory \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb')
      qed

      have tmps_distinct': "tmps_distinct ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_load_tmps is\<^sub>s\<^sub>b'" by (simp add: "is\<^sub>s\<^sub>b")
	from load_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b')
      next
	from read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "distinct_read_tmps (sb @ [Ghost\<^sub>s\<^sub>b A L R W])"
	  by (auto simp add: distinct_read_tmps_append)
	from read_tmps_distinct_nth_update [OF i_bound this]
	show "read_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb')
      next
	from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> read_tmps (sb @ [Ghost\<^sub>s\<^sub>b A L R W]) ={}"
	  by (auto simp add: read_tmps_append "is\<^sub>s\<^sub>b")
	from load_tmps_read_tmps_distinct_nth_update [OF i_bound this]
	show "load_tmps_read_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed
      
      have valid_sops': "valid_sops ts\<^sub>s\<^sub>b'"
      proof -
	from valid_store_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	obtain 
	  valid_store_sops': "\<forall>sop\<in>store_sops is\<^sub>s\<^sub>b'. valid_sop sop"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	from valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
	have valid_write_sops': "\<forall>sop\<in>write_sops (sb@ [Ghost\<^sub>s\<^sub>b A L R W]). 
	  valid_sop sop"
	  by (auto simp add: write_sops_append)
	from valid_sops_nth_update [OF i_bound  valid_write_sops' valid_store_sops']
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      have valid_dd': "valid_data_dependency ts\<^sub>s\<^sub>b'"
      proof -
	from data_dependency_consistent_instrs [OF i_bound ts\<^sub>s\<^sub>b_i]
	obtain 
	  dd_is: "data_dependency_consistent_instrs (dom \<theta>\<^sub>s\<^sub>b') is\<^sub>s\<^sub>b'"
	  by (auto simp add: "is\<^sub>s\<^sub>b" \<theta>\<^sub>s\<^sub>b')
	from load_tmps_write_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> \<Union>(fst ` write_sops (sb@ [Ghost\<^sub>s\<^sub>b A L R W])) ={}"
	  by (auto simp add: write_sops_append "is\<^sub>s\<^sub>b")
	from valid_data_dependency_nth_update [OF i_bound dd_is this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      have load_tmps_fresh': "load_tmps_fresh ts\<^sub>s\<^sub>b'"
      proof -
	from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "load_tmps is\<^sub>s\<^sub>b' \<inter> dom \<theta>\<^sub>s\<^sub>b = {}"
	  by (auto simp add: "is\<^sub>s\<^sub>b")
	from load_tmps_fresh_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b')
      qed

      have enough_flushs': "enough_flushs ts\<^sub>s\<^sub>b'"
      proof -
	from clean_no_outstanding_volatile_Write\<^sub>s\<^sub>b [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "\<not> \<D>\<^sub>s\<^sub>b \<longrightarrow> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Ghost\<^sub>s\<^sub>b A L R W])= {}"
	  by (auto simp add: outstanding_refs_append)
	from enough_flushs_nth_update [OF i_bound this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' sb' \<D>\<^sub>s\<^sub>b')
      qed
	

      have valid_program_history': "valid_program_history ts\<^sub>s\<^sub>b'"
      proof -	
	from valid_program_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "causal_program_history is\<^sub>s\<^sub>b sb" .
	then have causal': "causal_program_history is\<^sub>s\<^sub>b' (sb@[Ghost\<^sub>s\<^sub>b A L R W])"
	  by (auto simp: causal_program_history_Ghost  "is\<^sub>s\<^sub>b")
	from valid_last_prog [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "last_prog p\<^sub>s\<^sub>b sb = p\<^sub>s\<^sub>b".
	hence "last_prog p\<^sub>s\<^sub>b (sb @ [Ghost\<^sub>s\<^sub>b A L R W]) = p\<^sub>s\<^sub>b"
	  by (simp add: last_prog_append_Ghost\<^sub>s\<^sub>b)
	from valid_program_history_nth_update [OF i_bound causal' this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' sb')
      qed

      show ?thesis
      proof (cases "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}")
	case True

	from True have flush_all: "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = sb"
	  by (auto simp add: outstanding_refs_conv)
	
	from True have suspend_nothing: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = []"
	  by (auto simp add: outstanding_refs_conv)

	hence suspends_empty: "suspends = []"
	  by (simp add: suspends)

	from suspends_empty is_sim have "is": "is =Ghost A L R W# is\<^sub>s\<^sub>b'"
	  by (simp add: "is\<^sub>s\<^sub>b")

	with suspends_empty ts_i 
	have ts_i: "ts!i = (p\<^sub>s\<^sub>b, Ghost A L R W# is\<^sub>s\<^sub>b',
	  \<theta>\<^sub>s\<^sub>b,(), \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
	  by simp

	from direct_memop_step.Ghost 	
	have "(Ghost A L R W# is\<^sub>s\<^sub>b', 
	  \<theta>\<^sub>s\<^sub>b, (),m, \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b, 
               release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b, \<S>) \<rightarrow> 
               (is\<^sub>s\<^sub>b', 
	  \<theta>\<^sub>s\<^sub>b, (), m, \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b \<union> A - R, 
           augment_rels (dom \<S>) R (release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b),
           \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".
	from direct_computation.concurrent_step.Memop [OF i_bound' ts_i this]
	have "(ts, m, \<S>) \<Rightarrow>\<^sub>d 
              (ts[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b', 
	          \<theta>\<^sub>s\<^sub>b, (),\<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b \<union> A - R,
                  augment_rels (dom \<S>) R (release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b))], 
	       m,\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

	moreover

	from suspend_nothing
	have suspend_nothing': "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') = []"
	  by (simp add: sb')


	have all_shared_A: "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length ts\<^sub>s\<^sub>b \<longrightarrow> i \<noteq> j \<longrightarrow>
	  ts\<^sub>s\<^sub>b ! j = (p, is, \<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
	  all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> A = {}"
	proof -
	  {
	    fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	    assume neq_i_j: "i \<noteq> j"
	    assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j, \<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	    assume x_shared: "x \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    assume x_A: "x \<in> A"
	    have False
	    proof -
	      from all_shared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]
	      have "all_shared sb\<^sub>j \<subseteq> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j".

	      moreover have "all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<subseteq> all_shared sb\<^sub>j"
		using all_shared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
		by auto
	      moreover

	      from A_unaquired_by_others [rule_format, OF _ neq_i_j] jth j_bound
	      have "A \<inter> all_acquired sb\<^sub>j = {}" by auto
	      moreover

	      from A_unowned_by_others [rule_format, OF _ neq_i_j] jth j_bound
	      have "A \<inter> \<O>\<^sub>j = {}"
		by (auto dest: all_shared_acquired_in)


	      ultimately
	      show False
		using x_A x_shared
		by blast
	    qed
	  }
	  thus ?thesis by blast
	qed

	hence all_shared_L: "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length ts\<^sub>s\<^sub>b \<longrightarrow> i \<noteq> j \<longrightarrow>
	  ts\<^sub>s\<^sub>b ! j = (p, is, \<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
	  all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> L = {}"
	  using L_subset by blast

        have all_shared_A: "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length ts\<^sub>s\<^sub>b \<longrightarrow> i \<noteq> j \<longrightarrow>
            ts\<^sub>s\<^sub>b ! j = (p, is, \<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
            all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> A = {}"
        proof -
	  {
	    fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	    assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
            assume neq_i_j: "i \<noteq> j" 
	    assume x_shared: "x \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    assume x_A: "x \<in> A"
	    have False
	    proof -
	      from all_shared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]
	      have "all_shared sb\<^sub>j \<subseteq> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j".

	      moreover have "all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<subseteq> all_shared sb\<^sub>j"
		using all_shared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
		by auto
	      moreover
	      from A_unaquired_by_others [rule_format, OF _ neq_i_j] jth j_bound
	      have "A \<inter> all_acquired sb\<^sub>j = {}" by auto
	      moreover

	      from A_unowned_by_others [rule_format, OF _ neq_i_j] jth j_bound
	      have "A \<inter> \<O>\<^sub>j = {}"
	        by (auto dest: all_shared_acquired_in)


	      ultimately
	      show False
		using x_A x_shared 
		by blast
	    qed  
	  }
	  thus ?thesis by blast
        qed
        hence all_shared_L: "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length ts\<^sub>s\<^sub>b \<longrightarrow> i \<noteq> j \<longrightarrow>
            ts\<^sub>s\<^sub>b ! j = (p, is, \<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
            all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> L = {}"
	  using L_subset by blast

        have all_unshared_R: "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length ts\<^sub>s\<^sub>b \<longrightarrow> i \<noteq> j \<longrightarrow>
            ts\<^sub>s\<^sub>b ! j = (p, is, \<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
            all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}"
        proof -
	  {
	    fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b"
            assume neq_i_j: "i \<noteq> j"
	    assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	    assume x_unshared: "x \<in> all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    assume x_R: "x \<in> R"
	    have False
	    proof -
	      from unshared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]
	      have "all_unshared sb\<^sub>j \<subseteq> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j".

	      moreover have "all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<subseteq> all_unshared sb\<^sub>j"
		using all_unshared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
		by auto
	      moreover

	      note ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]

	      ultimately
	      show False
		using  R_acq x_R x_unshared acquired_all_acquired [of True sb \<O>\<^sub>s\<^sub>b]
                by blast
	    qed
	  }
	  thus ?thesis by blast
        qed

        have all_acquired_R: "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length ts\<^sub>s\<^sub>b \<longrightarrow> i \<noteq> j \<longrightarrow>
            ts\<^sub>s\<^sub>b ! j = (p, is, \<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
            all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}"
        proof -
	  {
	    fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	    assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
            assume neq_i_j: "i \<noteq> j" 
	    assume x_acq: "x \<in> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    assume x_R: "x \<in> R"
            have False
	    proof -

	      from x_acq have "x \<in> all_acquired sb\<^sub>j"
		using all_acquired_append [of "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j" 
		  "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j"]
		by auto
	      moreover
	      note ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
	      ultimately
	      show False
		using  R_acq x_R acquired_all_acquired [of True sb \<O>\<^sub>s\<^sub>b]
		by blast
	    qed
	  }
	  thus ?thesis by blast
        qed

        have all_shared_R: "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length ts\<^sub>s\<^sub>b \<longrightarrow> i \<noteq> j \<longrightarrow> 
            ts\<^sub>s\<^sub>b ! j = (p, is, \<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
            all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}"
        proof -
	  {
	    fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	    assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
            assume neq_i_j: "i \<noteq> j" 
	    assume x_shared: "x \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    assume x_R: "x \<in> R"
	    have False
	    proof -
	      from all_shared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]
	      have "all_shared sb\<^sub>j \<subseteq> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j".

	      moreover have "all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<subseteq> all_shared sb\<^sub>j"
		using all_shared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
		by auto
	      moreover
	      note ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
	      ultimately 
	      show False
		using R_acq x_R x_shared acquired_all_acquired [of True sb \<O>\<^sub>s\<^sub>b]
		by blast
	    qed
	  }
	  thus ?thesis by blast
        qed

	note share_commute = 
	  share_all_until_volatile_write_append_Ghost\<^sub>s\<^sub>b [OF True \<open>ownership_distinct ts\<^sub>s\<^sub>b\<close> \<open>sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close>
	  i_bound ts\<^sub>s\<^sub>b_i all_shared_L all_shared_A all_acquired_R all_unshared_R all_shared_R]
        
	from \<D>
	have \<D>': "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Ghost\<^sub>s\<^sub>b A L R W]) \<noteq>  {})"
	  by (auto simp: outstanding_refs_append)


        have "\<forall>a \<in> R. (a \<in> (dom (share sb \<S>\<^sub>s\<^sub>b)) ) = (a \<in> dom \<S>)"
        proof -
          {
            fix a
            assume a_R: "a \<in> R"
            have "(a \<in> (dom (share sb \<S>\<^sub>s\<^sub>b)) ) = (a \<in> dom \<S>)"
            proof -
              from a_R R_acq acquired_all_acquired [of True sb \<O>\<^sub>s\<^sub>b]
              have "a \<in> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
                by auto
              
              
              from  share_all_until_volatile_write_thread_local' [OF ownership_distinct_ts\<^sub>s\<^sub>b sharing_consis_ts\<^sub>s\<^sub>b i_bound ts\<^sub>s\<^sub>b_i this] suspend_nothing
              show ?thesis by (auto simp add: domIff \<S>)
            qed
          }
          then show ?thesis by auto
        qed
        from augment_rels_shared_exchange [OF this]
        have rel_commute:    
           "augment_rels (dom \<S>) R (release sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b) =
           release (sb @ [Ghost\<^sub>s\<^sub>b A L R W]) (dom \<S>\<^sub>s\<^sub>b') \<R>\<^sub>s\<^sub>b"
          by (clarsimp simp add: release_append \<S>\<^sub>s\<^sub>b')

	have "(ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> 
	   (ts[i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b', 
	       \<theta>\<^sub>s\<^sub>b,(), \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b \<union> A - R,
                augment_rels (dom \<S>) R (release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b))], 
                 m,\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	  apply (rule sim_config.intros) 
	  apply    (simp add: m ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb' \<theta>\<^sub>s\<^sub>b' flush_all_until_volatile_write_append_Ghost_commute [OF i_bound ts\<^sub>s\<^sub>b_i])
	  apply   (clarsimp simp add: \<S> \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' share_commute)
	  using  leq
	  apply  (simp add: ts\<^sub>s\<^sub>b')
	  using i_bound i_bound' ts_sim ts_i True \<D>'
	  apply (clarsimp simp add: Let_def nth_list_update 
	    outstanding_refs_conv ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb'  \<D>\<^sub>s\<^sub>b' suspend_nothing' flush_all rel_commute
	    acquired_append split: if_split_asm)
	  done	

	ultimately show ?thesis
	  using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' 
	    valid_sops'
            valid_dd' load_tmps_fresh' enough_flushs' 
	    valid_program_history' valid' m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b'
	  by auto
      next
	case False

	then obtain r where r_in: "r \<in> set sb" and volatile_r: "is_volatile_Write\<^sub>s\<^sub>b r"
	  by (auto simp add: outstanding_refs_conv)
	from takeWhile_dropWhile_real_prefix 
	[OF r_in, of  "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)", simplified, OF volatile_r] 
	obtain a' v' sb'' A'' L'' R'' W'' sop' where
	  sb_split: "sb = takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb @ Write\<^sub>s\<^sub>b True a' sop' v' A'' L'' R'' W''# sb''" 
	  and
	  drop: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = Write\<^sub>s\<^sub>b True a' sop' v' A'' L'' R'' W''# sb''"
	  apply (auto)
    subgoal for y ys
	  apply (case_tac y)
	  apply auto
	  done
	  done
	from drop suspends have suspends: "suspends = Write\<^sub>s\<^sub>b True a' sop' v' A'' L'' R'' W''# sb''"
	  by simp

	have "(ts, m, \<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts, m, \<S>)" by auto
	moreover

	have "Write\<^sub>s\<^sub>b True a' sop' v' A'' L'' R'' W''\<in> set sb"
	  by (subst sb_split) auto
	note drop_app = dropWhile_append1 
	[OF this, of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)", simplified]

	from takeWhile_append1 [where P="Not \<circ> is_volatile_Write\<^sub>s\<^sub>b", OF r_in] volatile_r
	have takeWhile_app: 
	  "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Ghost\<^sub>s\<^sub>b A L R W])) = (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
	  by simp

	note share_commute = share_all_until_volatile_write_append_Ghost\<^sub>s\<^sub>b' [OF False i_bound ts\<^sub>s\<^sub>b_i]
	
	from \<D>
	have \<D>': "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Ghost\<^sub>s\<^sub>b A L R W]) \<noteq>  {})"
	  by (auto simp: outstanding_refs_append)


	have "(ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> (ts,m,\<S>)"
	  apply (rule sim_config.intros) 
	  apply    (simp add: m flush_all_until_volatile_write_append_Ghost_commute [OF i_bound ts\<^sub>s\<^sub>b_i] ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' sb')
	  apply   (clarsimp simp add: \<S> \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' share_commute)
	  using  leq
	  apply  (simp add: ts\<^sub>s\<^sub>b')
	  using i_bound i_bound' ts_sim ts_i is_sim \<D>'
	  apply (clarsimp simp add: Let_def nth_list_update is_sim drop_app
	    read_tmps_append suspends 
	    prog_instrs_append_Ghost\<^sub>s\<^sub>b instrs_append_Ghost\<^sub>s\<^sub>b hd_prog_append_Ghost\<^sub>s\<^sub>b
	    drop "is\<^sub>s\<^sub>b" ts\<^sub>s\<^sub>b' sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<theta>\<^sub>s\<^sub>b' \<D>\<^sub>s\<^sub>b' takeWhile_app split: if_split_asm)
	  done
	ultimately show ?thesis
	  using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' valid_dd'
	    valid_sops' load_tmps_fresh' enough_flushs' 
	    valid_program_history' valid' m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' 
	  by (auto simp del: fun_upd_apply )
      qed	
    qed
  next
    case (StoreBuffer i p\<^sub>s\<^sub>b "is\<^sub>s\<^sub>b" \<theta>\<^sub>s\<^sub>b sb \<D>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b  \<R>\<^sub>s\<^sub>b sb' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b')
    then obtain 
      
      ts\<^sub>s\<^sub>b': "ts\<^sub>s\<^sub>b' = ts\<^sub>s\<^sub>b[i := (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b, sb', \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b',\<R>\<^sub>s\<^sub>b')]" and
      i_bound: "i < length ts\<^sub>s\<^sub>b" and
      ts\<^sub>s\<^sub>b_i: "ts\<^sub>s\<^sub>b ! i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b,sb, \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b)" and
      flush: "(m\<^sub>s\<^sub>b,sb,\<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<rightarrow>\<^sub>f 
              (m\<^sub>s\<^sub>b',sb',\<O>\<^sub>s\<^sub>b',\<R>\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b')" 
      by auto

    from sim obtain 
      m: "m = flush_all_until_volatile_write ts\<^sub>s\<^sub>b m\<^sub>s\<^sub>b" and
      \<S>: "\<S> = share_all_until_volatile_write ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b" and
      leq: "length ts\<^sub>s\<^sub>b = length ts" and
      ts_sim: "\<forall>i<length ts\<^sub>s\<^sub>b.
           let (p, is\<^sub>s\<^sub>b, \<theta>, sb,\<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b,\<R>) = ts\<^sub>s\<^sub>b ! i;
               suspends = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb
           in  \<exists>is \<D>. instrs suspends @ is\<^sub>s\<^sub>b = is @ prog_instrs suspends \<and> 
                          \<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {}) \<and>
               ts ! i =
                   (hd_prog p suspends, 
                    is,
                    \<theta> |` (dom \<theta> - read_tmps suspends), (),
                    \<D>, 
                    acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>\<^sub>s\<^sub>b,
                    release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) (dom \<S>\<^sub>s\<^sub>b) \<R>)"
      by cases blast

    from i_bound leq have i_bound': "i < length ts"
      by auto


    have split_sb: "sb = takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb @ dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb"
      (is "sb = ?take_sb@?drop_sb")
      by simp

    from ts_sim [rule_format, OF i_bound] ts\<^sub>s\<^sub>b_i obtain suspends "is" \<D> where
      suspends: "suspends = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb" and
      is_sim: "instrs suspends @ is\<^sub>s\<^sub>b = is @ prog_instrs suspends" and
      \<D>: "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {})" and
      ts_i: "ts ! i =
          (hd_prog p\<^sub>s\<^sub>b suspends, is,
           \<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b - read_tmps suspends), (),\<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,
           release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
      by (auto simp add: Let_def)

    from flush_step_preserves_valid [OF i_bound ts\<^sub>s\<^sub>b_i flush valid]
    have valid': "valid ts\<^sub>s\<^sub>b'" 
      by (simp add: ts\<^sub>s\<^sub>b')

    from flush obtain r where sb: "sb=r#sb'"
      by (cases) auto

    from valid_history [OF i_bound ts\<^sub>s\<^sub>b_i]
    have "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b sb) sb".
    then
    have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b sb') sb'"
      by (auto simp add: sb intro: history_consistent_hd_prog 
	split: memref.splits option.splits)
    from valid_history_nth_update [OF i_bound this]
    have valid_hist': "valid_history program_step ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b')

    from read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
    have dist_sb': "distinct_read_tmps sb'"
      by (simp add: sb split: memref.splits)

    have tmps_distinct': "tmps_distinct ts\<^sub>s\<^sub>b'"
    proof (intro_locales)
      from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "distinct_load_tmps is\<^sub>s\<^sub>b".
	
      from load_tmps_distinct_nth_update [OF i_bound this]
      show "load_tmps_distinct ts\<^sub>s\<^sub>b'"
	by (simp add: ts\<^sub>s\<^sub>b')
    next
      from read_tmps_distinct_nth_update [OF i_bound dist_sb']
      show "read_tmps_distinct ts\<^sub>s\<^sub>b'"
	by (simp add: ts\<^sub>s\<^sub>b')
    next
      from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "load_tmps is\<^sub>s\<^sub>b \<inter> read_tmps sb' = {}"
	by (auto simp add: sb split: memref.splits)
      from load_tmps_read_tmps_distinct_nth_update [OF i_bound this]
      show "load_tmps_read_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b')
    qed

    from load_tmps_write_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
    have "load_tmps is\<^sub>s\<^sub>b \<inter> \<Union>(fst ` write_sops sb') = {}"
      by (auto simp add: sb split: memref.splits)
    from valid_data_dependency_nth_update 
     [OF i_bound data_dependency_consistent_instrs [OF i_bound ts\<^sub>s\<^sub>b_i] this]
    have valid_dd': "valid_data_dependency ts\<^sub>s\<^sub>b'"
      by (simp add: ts\<^sub>s\<^sub>b')

    from valid_store_sops [OF i_bound ts\<^sub>s\<^sub>b_i] valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i] 
    valid_sops_nth_update [OF i_bound]
    have valid_sops': "valid_sops ts\<^sub>s\<^sub>b'"
      by (cases r) (auto simp add: sb ts\<^sub>s\<^sub>b')
    
    have load_tmps_fresh': "load_tmps_fresh ts\<^sub>s\<^sub>b'"
    proof -
      from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i] 
      have "load_tmps is\<^sub>s\<^sub>b \<inter> dom \<theta>\<^sub>s\<^sub>b = {}".
      from load_tmps_fresh_nth_update [OF i_bound this]
      show ?thesis by (simp add: ts\<^sub>s\<^sub>b')
    qed

    have enough_flushs': "enough_flushs ts\<^sub>s\<^sub>b'"
    proof -
      from clean_no_outstanding_volatile_Write\<^sub>s\<^sub>b [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "\<not> \<D>\<^sub>s\<^sub>b \<longrightarrow> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb' = {}"
	by (auto simp add: sb split: if_split_asm)
      from enough_flushs_nth_update [OF i_bound this]
      show ?thesis
	by (simp add: ts\<^sub>s\<^sub>b' sb)
    qed

    show ?thesis
    proof (cases r)
      case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
      from flush this
      have m\<^sub>s\<^sub>b': "m\<^sub>s\<^sub>b' = (m\<^sub>s\<^sub>b(a := v))"
	by cases (auto simp add: sb)

      have non_volatile_owned: "\<not> volatile \<longrightarrow> a \<in> \<O>\<^sub>s\<^sub>b"
      proof (cases volatile)
	case True thus ?thesis by simp
      next
	case False
	with outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "a \<in> \<O>\<^sub>s\<^sub>b"
	  by (simp add: sb Write\<^sub>s\<^sub>b)
	thus ?thesis by simp
      qed

      have a_unowned_by_others:
	"\<forall>j < length ts\<^sub>s\<^sub>b. i \<noteq> j \<longrightarrow> (let (_,_,_,sb\<^sub>j,_,\<O>\<^sub>j,_) = ts\<^sub>s\<^sub>b ! j in 
	a \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j)"
      proof (unfold Let_def, clarify del: notI)
	fix j p\<^sub>j "is\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j
	assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	assume neq: "i \<noteq> j"
	assume ts_j: "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	show "a \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	proof (cases volatile)
	  case True
	  from outstanding_volatile_writes_unowned_by_others [OF i_bound j_bound neq 
           ts\<^sub>s\<^sub>b_i ts_j] 
	  show ?thesis 
	    by (simp add: sb Write\<^sub>s\<^sub>b True)
	next
	  case False
	  with non_volatile_owned
	  have "a \<in> \<O>\<^sub>s\<^sub>b"
	    by simp
	  with ownership_distinct [OF i_bound j_bound neq ts\<^sub>s\<^sub>b_i ts_j]
	  show ?thesis
	    by blast
	qed
      qed

      from valid_reads [OF i_bound ts\<^sub>s\<^sub>b_i]
      have reads_consis: "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b sb" .


      {
	fix j 
	fix p\<^sub>j is\<^sub>s\<^sub>b\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>s\<^sub>b\<^sub>j \<theta>\<^sub>j sb\<^sub>j
	assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	assume ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b!j=(p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	assume neq_i_j: "i\<noteq>j"
	have "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	proof 
	  assume "a \<in> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	  hence "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    by (simp add: outstanding_refs_is_non_volatile_Write\<^sub>s\<^sub>b_takeWhile_conv)
	  hence "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
	    using outstanding_refs_append [of _ "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
	      "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
	    by auto
	  with non_volatile_owned_or_read_only_outstanding_non_volatile_writes 
	  [OF outstanding_non_volatile_refs_owned_or_read_only [OF j_bound ts\<^sub>s\<^sub>b_j]]
	  have "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	    by auto
	  with a_unowned_by_others [rule_format, OF j_bound neq_i_j]  ts\<^sub>s\<^sub>b_j
	  show False
	    by auto
	qed
      }
      note a_notin_others = this

	
      from a_notin_others
      have a_notin_others': 
	"\<forall>j < length ts\<^sub>s\<^sub>b. i \<noteq> j \<longrightarrow>
        (let (_,_,_,sb\<^sub>j,_,_,_) = ts\<^sub>s\<^sub>b!j in a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))"
	by (fastforce simp add: Let_def)
      

      
      obtain D f where sop: "sop=(D,f)" by (cases sop) auto
      from valid_history [OF i_bound ts\<^sub>s\<^sub>b_i] sop sb Write\<^sub>s\<^sub>b
      obtain D_tmps: "D \<subseteq> dom \<theta>\<^sub>s\<^sub>b" and f_v: "f \<theta>\<^sub>s\<^sub>b = v" and
	 D_sb': "D \<inter> read_tmps sb' = {}"
	by auto
      let ?\<theta> = "(\<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b - read_tmps sb'))"
      from D_tmps D_sb'
      have D_tmps': "D \<subseteq> dom ?\<theta>"
	by auto
      from valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i, rule_format, of sop]
      have "valid_sop sop"
	by (auto simp add: sb Write\<^sub>s\<^sub>b)
      from this [simplified sop]
      interpret valid_sop "(D,f)" .
      from D_tmps D_sb' 
      have "((dom \<theta>\<^sub>s\<^sub>b - read_tmps sb') \<inter> D) = D"
	by blast
      with valid_sop [OF refl D_tmps] valid_sop [OF refl D_tmps']  f_v 
      have f_v': "f ?\<theta> = v"
	by auto

      have valid_program_history': "valid_program_history ts\<^sub>s\<^sub>b'"
      proof -	
	from valid_program_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "causal_program_history is\<^sub>s\<^sub>b sb" .
	then have causal': "causal_program_history is\<^sub>s\<^sub>b sb'"
	  by (simp add: sb Write\<^sub>s\<^sub>b causal_program_history_def)

	from valid_last_prog [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "last_prog p\<^sub>s\<^sub>b sb = p\<^sub>s\<^sub>b".
	hence "last_prog p\<^sub>s\<^sub>b sb' = p\<^sub>s\<^sub>b"
	  by (simp add: sb Write\<^sub>s\<^sub>b)

	from valid_program_history_nth_update [OF i_bound causal' this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b')
      qed



      show ?thesis
      proof (cases volatile)
	case True
	note volatile = this
	from flush Write\<^sub>s\<^sub>b volatile
	obtain 
	  \<O>\<^sub>s\<^sub>b': "\<O>\<^sub>s\<^sub>b'=\<O>\<^sub>s\<^sub>b \<union> A - R" and
	  \<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'= \<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and
          \<R>\<^sub>s\<^sub>b': "\<R>\<^sub>s\<^sub>b' = Map.empty"
	  by cases (auto  simp add: sb)

	from sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i] 
	obtain 
	  A_shared_owned: "A \<subseteq> dom \<S>\<^sub>s\<^sub>b \<union> \<O>\<^sub>s\<^sub>b" and
	  L_subset: "L \<subseteq> A" and
	  A_R: "A \<inter> R = {}" and
	  R_owned: "R \<subseteq> \<O>\<^sub>s\<^sub>b"
	  by (clarsimp simp add: sb Write\<^sub>s\<^sub>b volatile)


	 
	from sb Write\<^sub>s\<^sub>b True have take_empty: "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = []"
	  by (auto simp add: outstanding_refs_conv)
	
	from sb Write\<^sub>s\<^sub>b True have suspend_all: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = sb"
	  by (auto simp add: outstanding_refs_conv)

	hence suspends_all: "suspends = sb"
	  by (simp add: suspends)

	from is_sim 
	have is_sim: "Write True a (D, f) A L R W# instrs sb' @ is\<^sub>s\<^sub>b = is @ prog_instrs sb'"
	  by (simp add: True Write\<^sub>s\<^sub>b suspends_all sb sop)

	from valid_program_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	interpret causal_program_history "is\<^sub>s\<^sub>b" sb .
	from valid_last_prog [OF i_bound ts\<^sub>s\<^sub>b_i]
	have last_prog: "last_prog p\<^sub>s\<^sub>b sb = p\<^sub>s\<^sub>b".

	from causal_program_history [of "[Write\<^sub>s\<^sub>b True a (D, f) v A L R W]" sb'] is_sim 
	obtain is' where 
	  "is": "is = Write True a (D, f) A L R W# is'" and
	  is'_sim: "instrs sb'@is\<^sub>s\<^sub>b = is' @ prog_instrs sb'" 
	  by (auto simp add: sb Write\<^sub>s\<^sub>b volatile sop)
	  
	from causal_program_history have
	  causal_program_history_sb': "causal_program_history is\<^sub>s\<^sub>b sb'"
	  apply -
	  apply (rule causal_program_history.intro)
	  apply (auto simp add: sb Write\<^sub>s\<^sub>b)
	  done

	from ts_i have ts_i: "ts ! i =
          (hd_prog p\<^sub>s\<^sub>b sb', Write True a (D, f) A L R W# is',  ?\<theta>, (), \<D>,acquired True ?take_sb \<O>\<^sub>s\<^sub>b,
           release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"	
	  by (simp add: suspends_all sb Write\<^sub>s\<^sub>b "is")

	let ?ts' = "ts[i := (hd_prog p\<^sub>s\<^sub>b sb', is', ?\<theta>, (), True, acquired True ?take_sb \<O>\<^sub>s\<^sub>b \<union> A - R,
                       Map.empty)]"

	from i_bound' have ts'_i: "?ts'!i = (hd_prog p\<^sub>s\<^sub>b sb', is', ?\<theta>, (),True, acquired True ?take_sb \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)" 
	  by simp

	from no_outstanding_write_to_read_only_memory [OF i_bound ts\<^sub>s\<^sub>b_i]
	have a_not_ro: "a \<notin> read_only \<S>\<^sub>s\<^sub>b"
	  by (clarsimp simp add: sb Write\<^sub>s\<^sub>b volatile)

	{
	  fix j 
	  fix p\<^sub>j is\<^sub>s\<^sub>b\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>s\<^sub>b\<^sub>j \<theta>\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	  assume ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b!j=(p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  assume neq_i_j: "i\<noteq>j"
	  have "a \<notin> unforwarded_non_volatile_reads (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) {}"
	  proof 
	    let ?take_sb\<^sub>j = "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j"
	    let ?drop_sb\<^sub>j = "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j"
	    assume a_in: "a \<in>  unforwarded_non_volatile_reads ?drop_sb\<^sub>j {}"
	    
	    from a_unowned_by_others [rule_format, OF j_bound neq_i_j] ts\<^sub>s\<^sub>b_j 
	    obtain a_unowned: "a \<notin> \<O>\<^sub>j" and a_unacq: "a \<notin> all_acquired sb\<^sub>j"
	      by auto
	    with all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j] acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b [of sb\<^sub>j \<O>\<^sub>j]
	    have a_unacq_take: "a \<notin> acquired True ?take_sb\<^sub>j \<O>\<^sub>j"
	      by (auto simp add: )

	    note nvo_j = outstanding_non_volatile_refs_owned_or_read_only [OF j_bound ts\<^sub>s\<^sub>b_j]
	  
	    from non_volatile_owned_or_read_only_drop [OF nvo_j]
	    have nvo_drop_j: "non_volatile_owned_or_read_only True (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)
	      (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j" .

	    note consis_j = sharing_consis [OF j_bound ts\<^sub>s\<^sub>b_j]
	    with sharing_consistent_append [of \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	    obtain consis_take_j: "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j ?take_sb\<^sub>j" and
	      consis_drop_j: "sharing_consistent (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)
	      (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
	      by auto

	    from in_unforwarded_non_volatile_reads_non_volatile_Read\<^sub>s\<^sub>b [OF a_in]
	    have a_in': "a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?drop_sb\<^sub>j".
	    
	    note reads_consis_j = valid_reads [OF j_bound ts\<^sub>s\<^sub>b_j]
	    from reads_consistent_drop [OF this]
	    have reads_consis_drop_j:
	      "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) (flush ?take_sb\<^sub>j m\<^sub>s\<^sub>b) ?drop_sb\<^sub>j".
	    

            
            from read_only_share_all_shared [of a ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b] a_not_ro 
              all_shared_acquired_or_owned [OF consis_take_j]
              all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j] a_unowned a_unacq
	    have a_not_ro_j: "a \<notin> read_only (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)"
              by auto
	    
	  
	    from ts_sim [rule_format, OF j_bound] ts\<^sub>s\<^sub>b_j j_bound
	    obtain suspends\<^sub>j "is\<^sub>j" \<D>\<^sub>j \<R>\<^sub>j where
	      suspends\<^sub>j: "suspends\<^sub>j = ?drop_sb\<^sub>j" and
	      is\<^sub>j: "instrs suspends\<^sub>j @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j @ prog_instrs suspends\<^sub>j" and
	      \<D>\<^sub>j: "\<D>\<^sub>s\<^sub>b\<^sub>j = (\<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<noteq> {})" and
	      ts\<^sub>j: "ts!j = (hd_prog p\<^sub>j suspends\<^sub>j, is\<^sub>j, 
	      \<theta>\<^sub>j |` (dom \<theta>\<^sub>j - read_tmps suspends\<^sub>j),(),   
	      \<D>\<^sub>j, acquired True ?take_sb\<^sub>j \<O>\<^sub>j,\<R>\<^sub>j)"
	      by (auto simp: Let_def)

	    from valid_last_prog [OF j_bound ts\<^sub>s\<^sub>b_j] have last_prog: "last_prog p\<^sub>j sb\<^sub>j = p\<^sub>j".
	    

	    from j_bound i_bound' leq have j_bound_ts': "j < length ts"
	      by simp
	    from read_only_read_acquired_unforwarded_acquire_witness [OF nvo_drop_j consis_drop_j
	      a_not_ro_j a_unacq_take a_in]

	    have False
	    proof
	      assume "\<exists>sop a' v ys zs A L R W. 
		?drop_sb\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W # zs \<and> a \<in> A \<and> 
		a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys \<and> a'\<noteq>a"
	      with suspends\<^sub>j 
	      obtain a' sop' v' ys zs' A' L' R' W' where
		split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# zs'" (is "suspends\<^sub>j=?suspends") and
		a_A': "a \<in> A'" and
		no_write: "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (ys @ [Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'])"
		by (auto simp add: outstanding_refs_append)

	      from last_prog
	      have lp: "last_prog p\<^sub>j suspends\<^sub>j = p\<^sub>j"
		apply -
		apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply simp
		done

	      from sharing_consis [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have sharing_consis_j: "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	      then have A'_R': "A' \<inter> R' = {}" 
		by (simp add: sharing_consistent_append [of _ _ ?take_sb\<^sub>j ?drop_sb\<^sub>j, simplified] 
		  suspends\<^sub>j [symmetric] split_suspends\<^sub>j sharing_consistent_append)	  
	      
	      from valid_program_history [OF j_bound ts\<^sub>s\<^sub>b_j] 
	      have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	      then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
		apply -
		apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply (simp add: split_suspends\<^sub>j)
		done
	      
	      from valid_reads [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have reads_consis_j: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	      
	      from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> 
		j_bound ts\<^sub>s\<^sub>b_j this]
	      have reads_consis_m_j: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
		by (simp add: m suspends\<^sub>j)
	    
	      hence reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)  
		m (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'])"
		by (simp add: split_suspends\<^sub>j reads_consistent_append)

	      from valid_write_sops [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		valid_sops_drop: "\<forall>sop\<in>write_sops (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']). valid_sop sop"
		apply (simp only: write_sops_append)
		apply auto
		done
	    
	      from read_tmps_distinct [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      then obtain 
		read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
		distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		apply (simp only: distinct_read_tmps_append)
		done
	    
	      from valid_history [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have h_consis: 
		"history_consistent \<theta>\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply simp
		done
	      
	      have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	      proof -
		from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		  by simp
		from last_prog_hd_prog_append' [OF h_consis] this
		have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		  by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		moreover 
		have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		  last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		  apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		  by (rule last_prog_hd_prog_append)
		ultimately show ?thesis
		  by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      qed

	      from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
		h_consis] last_prog_hd_prog
	      have hist_consis': "history_consistent \<theta>\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      from reads_consistent_drop_volatile_writes_no_volatile_reads  
	      [OF reads_consis_j] 
	      have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b 
		(ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) = {}"
		by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		split_suspends\<^sub>j )
	    
	      have acq_simp:
		"acquired True (ys @ [Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) 
		(acquired True ?take_sb\<^sub>j \<O>\<^sub>j) = 
		acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R'"
		by (simp add: acquired_append)

	      from flush_store_buffer_append [where sb="ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']" and sb'="zs'", simplified,
	      OF j_bound_ts' is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]  ts\<^sub>j [simplified split_suspends\<^sub>j]
	      refl lp [simplified split_suspends\<^sub>j] reads_consis_ys 	      
	      hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
	      distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
	      no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
	      \<S>="\<S>"]
	    
	      obtain is\<^sub>j' \<R>\<^sub>j' where
		is\<^sub>j': "instrs zs' @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs'" and
		steps_ys: "(ts, m, \<S>)  \<Rightarrow>\<^sub>d\<^sup>* 
		  (ts[j:=(last_prog
                              (hd_prog p\<^sub>j (Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# zs')) (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']),
                             is\<^sub>j',
                             \<theta>\<^sub>j |` (dom \<theta>\<^sub>j - read_tmps zs'),
                              (), True, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R',\<R>\<^sub>j')],
                    flush (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) m,
                    share (ys@[Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W']) \<S>)"
		(is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
		by (auto simp add: acquired_append outstanding_refs_append)

	      from i_bound' have i_bound_ys: "i < length ?ts_ys"
		by auto
	    
	      from i_bound' neq_i_j  ts_i
	      have ts_ys_i: "?ts_ys!i = (hd_prog p\<^sub>s\<^sub>b sb', Write True a (D, f) A L R W# is', ?\<theta>, (), \<D>, 
		acquired True ?take_sb \<O>\<^sub>s\<^sub>b,release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
		by simp
	      
	      note conflict_computation = steps_ys
	      
	      from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	      have safe: "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	      
	      with safe_delayedE [OF safe i_bound_ys ts_ys_i] 
	      have a_unowned: 
		"\<forall>j < length ?ts_ys. i\<noteq>j \<longrightarrow> (let (\<O>\<^sub>j) = map owned ?ts_ys!j in a \<notin> \<O>\<^sub>j)"
		apply cases
		apply (auto simp add: Let_def sb)
		done
	      from a_A' a_unowned [rule_format, of j] neq_i_j j_bound leq A'_R'
	      show False
		by (auto simp add: Let_def)
	    next
	      assume "\<exists>A L R W ys zs. ?drop_sb\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b ys"
	      with suspends\<^sub>j 
	      obtain ys zs' A' L' R' W' where
		split_suspends\<^sub>j: "suspends\<^sub>j = ys @ Ghost\<^sub>s\<^sub>b A' L' R' W'# zs'" (is "suspends\<^sub>j=?suspends") and
		a_A': "a \<in> A'" and
		no_write: "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W'])"
		by (auto simp add: outstanding_refs_append)

	      from last_prog
	      have lp: "last_prog p\<^sub>j suspends\<^sub>j = p\<^sub>j"
		apply -
		apply (rule last_prog_same_append [where sb="?take_sb\<^sub>j"])
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply simp
		done


	      from valid_program_history [OF j_bound ts\<^sub>s\<^sub>b_j] 
	      have "causal_program_history is\<^sub>s\<^sub>b\<^sub>j sb\<^sub>j".
	      then have cph: "causal_program_history is\<^sub>s\<^sub>b\<^sub>j ?suspends"
		apply -
		apply (rule causal_program_history_suffix [where sb="?take_sb\<^sub>j"] )
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply (simp add: split_suspends\<^sub>j)
		done
	    
	      from valid_reads [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have reads_consis_j: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j".
	    
	      from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> 
		j_bound ts\<^sub>s\<^sub>b_j this]
	      have reads_consis_m_j: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) m suspends\<^sub>j"
		by (simp add: m suspends\<^sub>j)
	    
	    
	      hence reads_consis_ys: "reads_consistent True (acquired True ?take_sb\<^sub>j \<O>\<^sub>j)  
		m (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W'])"
		by (simp add: split_suspends\<^sub>j reads_consistent_append)

	      from valid_write_sops [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have "\<forall>sop\<in>write_sops (?take_sb\<^sub>j@?suspends). valid_sop sop"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      then obtain valid_sops_take: "\<forall>sop\<in>write_sops ?take_sb\<^sub>j. valid_sop sop" and
		valid_sops_drop: "\<forall>sop\<in>write_sops (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']). valid_sop sop"
		apply (simp only: write_sops_append)
		apply auto
		done
	      
	      from read_tmps_distinct [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have "distinct_read_tmps (?take_sb\<^sub>j@suspends\<^sub>j)"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      then obtain 
		read_tmps_take_drop: "read_tmps ?take_sb\<^sub>j \<inter> read_tmps suspends\<^sub>j = {}" and
		distinct_read_tmps_drop: "distinct_read_tmps suspends\<^sub>j"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		apply (simp only: distinct_read_tmps_append)
		done
	    
	      from valid_history [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have h_consis: 
		"history_consistent \<theta>\<^sub>j (hd_prog p\<^sub>j (?take_sb\<^sub>j@suspends\<^sub>j)) (?take_sb\<^sub>j@suspends\<^sub>j)"
		apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
		apply simp
		done
	    
	      from sharing_consis [OF j_bound ts\<^sub>s\<^sub>b_j]
	      have sharing_consis_j: "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	      then have A'_R': "A' \<inter> R' = {}" 
		by (simp add: sharing_consistent_append [of _ _ ?take_sb\<^sub>j ?drop_sb\<^sub>j, simplified] 
		  suspends\<^sub>j [symmetric] split_suspends\<^sub>j sharing_consistent_append)	  

	      have last_prog_hd_prog: "last_prog (hd_prog p\<^sub>j sb\<^sub>j) ?take_sb\<^sub>j = (hd_prog p\<^sub>j suspends\<^sub>j)"
	      proof -
		from last_prog have "last_prog p\<^sub>j (?take_sb\<^sub>j@?drop_sb\<^sub>j) = p\<^sub>j"
		  by simp
		from last_prog_hd_prog_append' [OF h_consis] this
		have "last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j = hd_prog p\<^sub>j suspends\<^sub>j"
		  by (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		moreover 
		have "last_prog (hd_prog p\<^sub>j (?take_sb\<^sub>j @ suspends\<^sub>j)) ?take_sb\<^sub>j = 
		  last_prog (hd_prog p\<^sub>j suspends\<^sub>j) ?take_sb\<^sub>j"
		  apply (simp only: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
		  by (rule last_prog_hd_prog_append)
		ultimately show ?thesis
		  by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j) 
	      qed
	      
	      from history_consistent_appendD [OF valid_sops_take read_tmps_take_drop 
		h_consis] last_prog_hd_prog
	      have hist_consis': "history_consistent \<theta>\<^sub>j (hd_prog p\<^sub>j suspends\<^sub>j) suspends\<^sub>j"
		by (simp add: split_suspends\<^sub>j [symmetric] suspends\<^sub>j)
	      from reads_consistent_drop_volatile_writes_no_volatile_reads  
	      [OF reads_consis_j] 
	      have no_vol_read: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b 
	      (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) = {}"
		by (auto simp add: outstanding_refs_append suspends\<^sub>j [symmetric] 
		  split_suspends\<^sub>j )
	    
	      have acq_simp:
		"acquired True (ys @ [Ghost\<^sub>s\<^sub>b A' L' R' W']) 
		(acquired True ?take_sb\<^sub>j \<O>\<^sub>j) = 
		acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R'"
		by (simp add: acquired_append)
	    
	      from flush_store_buffer_append [where sb="ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']" and sb'="zs'", simplified,
		OF j_bound_ts' is\<^sub>j [simplified split_suspends\<^sub>j] cph [simplified suspends\<^sub>j]
		ts\<^sub>j [simplified split_suspends\<^sub>j] refl lp [simplified split_suspends\<^sub>j] reads_consis_ys 
		hist_consis' [simplified split_suspends\<^sub>j] valid_sops_drop 
		distinct_read_tmps_drop [simplified split_suspends\<^sub>j] 
		no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_vol_read], where
		\<S>="\<S>"]
	      
	      obtain is\<^sub>j' \<R>\<^sub>j' where
		is\<^sub>j': "instrs zs' @ is\<^sub>s\<^sub>b\<^sub>j = is\<^sub>j' @ prog_instrs zs'" and
		steps_ys: "(ts, m,\<S>)  \<Rightarrow>\<^sub>d\<^sup>* 
		  (ts[j:=(last_prog
                              (hd_prog p\<^sub>j (Ghost\<^sub>s\<^sub>b A' L' R' W'# zs')) (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']),
                             is\<^sub>j',
                             \<theta>\<^sub>j |` (dom \<theta>\<^sub>j - read_tmps zs'),
                              (), 
	                     \<D>\<^sub>j \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ys \<noteq> {}, acquired True ys (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) \<union> A' - R',\<R>\<^sub>j')],
                    flush (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) m,                    share (ys@[Ghost\<^sub>s\<^sub>b A' L' R' W']) \<S>)"
		(is "(_,_,_) \<Rightarrow>\<^sub>d\<^sup>* (?ts_ys,?m_ys,?shared_ys)")
		by (auto simp add: acquired_append outstanding_refs_append)

	      from i_bound' have i_bound_ys: "i < length ?ts_ys"
		by auto
	      
	      from i_bound' neq_i_j  ts_i
	      have ts_ys_i: "?ts_ys!i = (hd_prog p\<^sub>s\<^sub>b sb', Write True a (D, f) A L R W# is', ?\<theta>, (), \<D>, 
		acquired True ?take_sb \<O>\<^sub>s\<^sub>b,release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
		by simp

	      note conflict_computation = steps_ys
	    
	      from safe_reach_safe_rtrancl [OF safe_reach conflict_computation]
	      have safe: "safe_delayed (?ts_ys,?m_ys,?shared_ys)".
	          
	      with safe_delayedE [OF safe i_bound_ys ts_ys_i] 
	      have a_unowned: 
		
		"\<forall>j < length ?ts_ys. i\<noteq>j \<longrightarrow> (let (\<O>\<^sub>j) = map owned ?ts_ys!j in a \<notin> \<O>\<^sub>j)"
		apply cases
		apply (auto simp add: Let_def sb)
		done
	      from a_A' a_unowned [rule_format, of j] neq_i_j j_bound leq A'_R'
	      show False
		by (auto simp add: Let_def)
	    qed
	    then show False
	      by simp
	  qed
	}
	note a_notin_unforwarded_non_volatile_reads_drop = this


	have valid_reads': "valid_reads m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)
	  fix j p\<^sub>j "is\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume ts_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b' sb\<^sub>j"
	  proof (cases "i=j")
	    case True
	    from reads_consis ts_j j_bound sb show ?thesis
	      by (clarsimp simp add: True  m\<^sub>s\<^sub>b' Write\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' volatile reads_consistent_pending_write_antimono)
	  next
	    case False
	    from j_bound have j_bound':  "j < length ts\<^sub>s\<^sub>b"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    moreover from ts_j False have ts_j': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      using j_bound by (simp add: ts\<^sub>s\<^sub>b')
	    ultimately have consis_m: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j"
	      by (rule valid_reads)
	    from a_unowned_by_others [rule_format, OF j_bound' False] ts_j'
	    have a_unowned:"a \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	      by simp

	    let ?take_sb\<^sub>j = "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j"
	    let ?drop_sb\<^sub>j = "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j"

	    from a_unowned acquired_reads_all_acquired [of True ?take_sb\<^sub>j \<O>\<^sub>j]
	    all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	    have a_not_acq_reads: "a \<notin> acquired_reads True ?take_sb\<^sub>j \<O>\<^sub>j"
	      by auto
	    moreover
	    note a_unfw= a_notin_unforwarded_non_volatile_reads_drop [OF j_bound' ts_j' False]
	    ultimately
	    show ?thesis
	      using reads_consistent_mem_eq_on_unforwarded_non_volatile_reads_drop [where W="{}" and 
		A="unforwarded_non_volatile_reads ?drop_sb\<^sub>j {} \<union> acquired_reads True ?take_sb\<^sub>j \<O>\<^sub>j" and
		m'= "(m\<^sub>s\<^sub>b(a:=v))", OF _ _ _ consis_m]
	      by (fastforce simp add: m\<^sub>s\<^sub>b')
	  qed
	qed
       

	have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof (intro_locales)
	  show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  proof 
	    fix j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j p\<^sub>j
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	    assume ts\<^sub>s\<^sub>b'_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	    show "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b' \<O>\<^sub>j sb\<^sub>j"
	    proof (cases "j=i")
	      case True
	      from outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i]
	      have "non_volatile_owned_or_read_only False 
	        (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O>\<^sub>s\<^sub>b \<union> A - R) sb'"
		by (auto simp add: sb Write\<^sub>s\<^sub>b volatile non_volatile_owned_or_read_only_pending_write_antimono)
	      then show ?thesis
		using True i_bound ts\<^sub>s\<^sub>b'_j
		by (auto simp add: ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' sb \<O>\<^sub>s\<^sub>b')
	    next
	      case False
	      from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      with ts\<^sub>s\<^sub>b'_j False i_bound 
	      have ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      
	      
	      note nvo = outstanding_non_volatile_refs_owned_or_read_only [OF j_bound' ts\<^sub>s\<^sub>b_j]

	      from read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] R_owned
	      have "R \<inter> read_only \<S>\<^sub>s\<^sub>b = {}"
		by auto
	      with read_only_reads_unowned [OF j_bound' i_bound False ts\<^sub>s\<^sub>b_j ts\<^sub>s\<^sub>b_i] L_subset
	      have "\<forall>a\<in>read_only_reads
	      (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j)
		(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j).
		a \<in> read_only \<S>\<^sub>s\<^sub>b \<longrightarrow> a \<in> read_only (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
		by (auto simp add: in_read_only_convs sb Write\<^sub>s\<^sub>b volatile)
	      from non_volatile_owned_or_read_only_read_only_reads_eq' [OF nvo this]
	      have "non_volatile_owned_or_read_only False (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<O>\<^sub>j sb\<^sub>j".
	      thus ?thesis by (simp add: \<S>\<^sub>s\<^sub>b')
	    qed
	  qed
	next
	  show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'"
	  proof (unfold_locales)
	    fix i\<^sub>1 j p\<^sub>1 "is\<^sub>1" \<O>\<^sub>1 \<R>\<^sub>1 \<D>\<^sub>1 xs\<^sub>1 sb\<^sub>1 p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	    assume i\<^sub>1_bound: "i\<^sub>1 < length ts\<^sub>s\<^sub>b'"
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	    assume i\<^sub>1_j: "i\<^sub>1 \<noteq> j"
	    assume ts_i\<^sub>1: "ts\<^sub>s\<^sub>b'!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	    assume ts_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j, xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	    show "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}"
	    proof (cases "i\<^sub>1=i")
	      case True
	      from i\<^sub>1_j True have neq_i_j: "i\<noteq>j"
		by auto
	      from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from ts_j neq_i_j have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from outstanding_volatile_writes_unowned_by_others [OF i_bound j_bound' neq_i_j
		ts\<^sub>s\<^sub>b_i ts_j'] ts_i\<^sub>1 i_bound ts\<^sub>s\<^sub>b_i True show ?thesis
		by (clarsimp simp add: ts\<^sub>s\<^sub>b' sb Write\<^sub>s\<^sub>b volatile)
	    next
	      case False
	      note i\<^sub>1_i = this
	      from i\<^sub>1_bound have i\<^sub>1_bound': "i\<^sub>1 < length ts\<^sub>s\<^sub>b"
		by (simp add: ts\<^sub>s\<^sub>b' sb)
	      hence i\<^sub>1_bound'': "i\<^sub>1 < length (map owned ts\<^sub>s\<^sub>b)"
		by auto
	      from ts_i\<^sub>1 False have ts_i\<^sub>1': "ts\<^sub>s\<^sub>b!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
		by (simp add: ts\<^sub>s\<^sub>b' sb)
	      show ?thesis
	      proof (cases "j=i")
		case True
		from outstanding_volatile_writes_unowned_by_others [OF i\<^sub>1_bound' i_bound  i\<^sub>1_i  ts_i\<^sub>1' ts\<^sub>s\<^sub>b_i ]
		have "(\<O>\<^sub>s\<^sub>b \<union> all_acquired sb) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}".
		then show ?thesis
		  using True i\<^sub>1_i ts_j ts\<^sub>s\<^sub>b_i i_bound
		  by (auto simp add: sb Write\<^sub>s\<^sub>b volatile ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b')
	      next
		case False
		from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		  by (simp add: ts\<^sub>s\<^sub>b')
		from ts_j False have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		  by (simp add: ts\<^sub>s\<^sub>b')
		from outstanding_volatile_writes_unowned_by_others 
		[OF i\<^sub>1_bound' j_bound' i\<^sub>1_j ts_i\<^sub>1' ts_j']
		show "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}" .
	      qed
	    qed
	  qed
	next
	  show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
	  proof 
	    fix n m
	    fix p\<^sub>n "is\<^sub>n" \<O>\<^sub>n \<R>\<^sub>n \<D>\<^sub>n \<theta>\<^sub>n sb\<^sub>n p\<^sub>m "is\<^sub>m" \<O>\<^sub>m \<R>\<^sub>m \<D>\<^sub>m \<theta>\<^sub>m sb\<^sub>m
	    assume n_bound: "n < length ts\<^sub>s\<^sub>b'"
	      and m_bound: "m < length ts\<^sub>s\<^sub>b'"
	      and neq_n_m: "n\<noteq>m"
	      and nth: "ts\<^sub>s\<^sub>b'!n = (p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
	      and mth: "ts\<^sub>s\<^sub>b'!m =(p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m,\<R>\<^sub>m)"
	    from n_bound have n_bound': "n < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')
	    from m_bound have m_bound': "m < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')
	    show "(\<O>\<^sub>m \<union> all_acquired sb\<^sub>m) \<inter>
              read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) \<O>\<^sub>n)
              (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) =
              {}"
	    proof (cases "m=i")
	      case True
	      with neq_n_m have neq_n_i: "n\<noteq>i"
		by auto
	      
	      with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      note read_only_reads_unowned [OF n_bound' i_bound  neq_n_i nth' ts\<^sub>s\<^sub>b_i]
	      then
	      show ?thesis
		using True ts\<^sub>s\<^sub>b_i neq_n_i nth mth n_bound' m_bound' L_subset
		by (auto simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb Write\<^sub>s\<^sub>b volatile)
	    next
	      case False
	      note neq_m_i = this
	      with m_bound mth i_bound have mth': "ts\<^sub>s\<^sub>b!m = (p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m,\<R>\<^sub>m)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      show ?thesis
	      proof (cases "n=i")
		case True
		from read_only_reads_append [of "(\<O>\<^sub>s\<^sub>b \<union> A - R)" "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n)"
		  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n)"]
		have "read_only_reads
                  (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) (\<O>\<^sub>s\<^sub>b \<union> A - R))
                  (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) \<subseteq> read_only_reads (\<O>\<^sub>s\<^sub>b \<union> A - R) sb\<^sub>n"
		  by auto
		
		with ts\<^sub>s\<^sub>b_i nth mth neq_m_i n_bound' True
		  read_only_reads_unowned [OF i_bound m_bound' False [symmetric] ts\<^sub>s\<^sub>b_i mth']
		show ?thesis
		  by (auto simp add: ts\<^sub>s\<^sub>b'  sb \<O>\<^sub>s\<^sub>b' Write\<^sub>s\<^sub>b volatile)
	      next
		case False
		with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
		  by (auto simp add: ts\<^sub>s\<^sub>b')
		from read_only_reads_unowned [OF n_bound' m_bound' neq_n_m  nth' mth'] False neq_m_i
		show ?thesis 
		  by (clarsimp)
	      qed
	    qed
	  qed
	next
	  show "ownership_distinct ts\<^sub>s\<^sub>b'"
	  proof (unfold_locales)
	    fix i\<^sub>1 j p\<^sub>1 "is\<^sub>1" \<O>\<^sub>1 \<R>\<^sub>1 \<D>\<^sub>1 xs\<^sub>1 sb\<^sub>1 p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	    assume i\<^sub>1_bound: "i\<^sub>1 < length ts\<^sub>s\<^sub>b'"
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	    assume i\<^sub>1_j: "i\<^sub>1 \<noteq> j"
	    assume ts_i\<^sub>1: "ts\<^sub>s\<^sub>b'!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	    assume ts_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	    show "(\<O>\<^sub>1 \<union> all_acquired sb\<^sub>1) \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j)= {}"
	    proof (cases "i\<^sub>1=i")
	      case True
	      with i\<^sub>1_j have i_j: "i\<noteq>j" 
		by simp
	      
	      from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		by (simp add: ts\<^sub>s\<^sub>b')
	      hence j_bound'': "j < length (map owned ts\<^sub>s\<^sub>b)"
		by simp	    
	      from ts_j i_j have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		by (simp add: ts\<^sub>s\<^sub>b')
	      
	      from ownership_distinct [OF i_bound j_bound' i_j ts\<^sub>s\<^sub>b_i ts_j']
	      show ?thesis
		using ts\<^sub>s\<^sub>b_i True ts_i\<^sub>1 i_bound \<O>\<^sub>s\<^sub>b'
		by (auto simp add: ts\<^sub>s\<^sub>b' sb Write\<^sub>s\<^sub>b volatile)
	    next
	      case False
	      note i\<^sub>1_i = this
	      from i\<^sub>1_bound have i\<^sub>1_bound': "i\<^sub>1 < length ts\<^sub>s\<^sub>b"
		by (simp add: ts\<^sub>s\<^sub>b')
	      hence i\<^sub>1_bound'': "i\<^sub>1 < length (map owned ts\<^sub>s\<^sub>b)"
		by simp	    
	      from ts_i\<^sub>1 False have ts_i\<^sub>1': "ts\<^sub>s\<^sub>b!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
		by (simp add: ts\<^sub>s\<^sub>b')
	      show ?thesis
	      proof (cases "j=i")
		case True
		from ownership_distinct [OF i\<^sub>1_bound' i_bound  i\<^sub>1_i ts_i\<^sub>1' ts\<^sub>s\<^sub>b_i]
		show ?thesis
		  using ts\<^sub>s\<^sub>b_i True ts_j i_bound \<O>\<^sub>s\<^sub>b'
		  by (auto simp add: ts\<^sub>s\<^sub>b' sb Write\<^sub>s\<^sub>b volatile)
	      next
		case False
		from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		  by (simp add: ts\<^sub>s\<^sub>b')
		from ts_j False have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		  by (simp add: ts\<^sub>s\<^sub>b')
		from ownership_distinct [OF i\<^sub>1_bound' j_bound' i\<^sub>1_j ts_i\<^sub>1' ts_j']
		show ?thesis .
	      qed
	    qed
	  qed
	qed

	have valid_sharing': "valid_sharing (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	proof (intro_locales)	
	  show "outstanding_non_volatile_writes_unshared (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	  proof (unfold_locales)
	    fix j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j acq\<^sub>j xs\<^sub>j sb\<^sub>j
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	    assume jth: "ts\<^sub>s\<^sub>b' ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	    show "non_volatile_writes_unshared (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)  sb\<^sub>j"
	    proof (cases "i=j")
	      case True
	      with outstanding_non_volatile_writes_unshared [OF i_bound ts\<^sub>s\<^sub>b_i]
		i_bound jth ts\<^sub>s\<^sub>b_i show ?thesis
		by (clarsimp simp add: ts\<^sub>s\<^sub>b' sb Write\<^sub>s\<^sub>b volatile)
	    next
	      case False
	      from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      from jth False have jth': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      from outstanding_non_volatile_writes_unshared [OF j_bound' jth']
	      have unshared: "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b sb\<^sub>j".
	      
	      have "\<forall>a\<in>dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom \<S>\<^sub>s\<^sub>b. a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
	      proof -
		{
		  fix a 
		  assume a_in: "a \<in> dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom \<S>\<^sub>s\<^sub>b"
		  hence a_R: "a \<in> R"
		    by clarsimp
		  assume a_in_j: "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
		  have False
		  proof -
		    from non_volatile_owned_or_read_only_outstanding_non_volatile_writes [OF
		      outstanding_non_volatile_refs_owned_or_read_only [OF j_bound' jth']]
		      a_in_j
		    have "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
		      by auto

		    moreover
		    with ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth'] a_R R_owned
		    show False
		      by blast
		  qed
		}
		thus ?thesis by blast
	      qed
		  
		

	      from non_volatile_writes_unshared_no_outstanding_non_volatile_Write\<^sub>s\<^sub>b 
	      [OF unshared this]
	      show ?thesis .
	    qed
	  qed
	next
	  show "sharing_consis (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	  proof (unfold_locales)  
	    fix j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	    assume jth: "ts\<^sub>s\<^sub>b' ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	    show "sharing_consistent (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<O>\<^sub>j sb\<^sub>j"
	    proof (cases "i=j")
	      case True
	      with i_bound jth ts\<^sub>s\<^sub>b_i sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]
	      show ?thesis
		by (clarsimp simp add: ts\<^sub>s\<^sub>b' sb Write\<^sub>s\<^sub>b volatile \<O>\<^sub>s\<^sub>b')
	    next
	      case False
	      from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      from jth False have jth': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      from sharing_consis [OF j_bound' jth']
	      have consis: "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	      
	      have acq_cond: "all_acquired sb\<^sub>j \<inter> dom \<S>\<^sub>s\<^sub>b - dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	      proof -
		{
		  fix a
		  assume a_acq: "a \<in> all_acquired sb\<^sub>j" 
		  assume "a \<in> dom \<S>\<^sub>s\<^sub>b" 
		  assume a_L: "a \<in> L"
		  have False
		  proof -
		    from ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth']
		    have "A \<inter> all_acquired sb\<^sub>j = {}"
		      by (auto simp add: sb Write\<^sub>s\<^sub>b volatile)
		    with a_acq a_L L_subset
		    show False
		      by blast
		  qed
		}
		thus ?thesis
		  by auto
	      qed
	      have uns_cond: "all_unshared sb\<^sub>j \<inter> dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom \<S>\<^sub>s\<^sub>b = {}"
	      proof -
		{
		  fix a
		  assume a_uns: "a \<in> all_unshared sb\<^sub>j" 
		  assume "a \<notin> L" 
		  assume a_R:  "a \<in> R"
		  have False
		  proof -
		    from unshared_acquired_or_owned [OF consis] a_uns
		    have "a \<in> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j" by auto
		    with ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth']  R_owned a_R
		    show False
		      by blast
		  qed
		}
		thus ?thesis
		  by auto
	      qed
	      
	      from sharing_consistent_preservation [OF consis acq_cond uns_cond]
	      show ?thesis
		by (simp add: ts\<^sub>s\<^sub>b')
	    qed
	  qed
	next
	  show "read_only_unowned (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	  proof 
	    fix j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j  \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	    assume jth: "ts\<^sub>s\<^sub>b' ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	    show "\<O>\<^sub>j \<inter> read_only (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	    proof (cases "i=j")
	      case True
	      from read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] R_owned  A_R 
	      have "(\<O>\<^sub>s\<^sub>b \<union> A - R) \<inter> read_only (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
		by (auto simp add: in_read_only_convs )
	      with jth ts\<^sub>s\<^sub>b_i i_bound True
	      show ?thesis
		by (auto simp add: \<O>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b')
	    next
	      case False
	      from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      with False jth have jth': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      from read_only_unowned [OF j_bound' jth']
	      have "\<O>\<^sub>j \<inter> read_only \<S>\<^sub>s\<^sub>b = {}".
	      moreover
	      from ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth'] R_owned
	      have "(\<O>\<^sub>s\<^sub>b \<union> A) \<inter> \<O>\<^sub>j = {}"
		by (auto simp add: sb Write\<^sub>s\<^sub>b volatile)
	      moreover note R_owned A_R
	      ultimately show ?thesis
		by (fastforce simp add: in_read_only_convs split: if_split_asm)
	    qed
	  qed
	next
	  show "unowned_shared (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	  proof (unfold_locales)
	    show "- \<Union>((\<lambda>(_,_, _, _,_, \<O>,_). \<O>) ` set ts\<^sub>s\<^sub>b') \<subseteq> dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	    proof -
	      
	      have s: "\<Union>((\<lambda>(_,_, _, _,_, \<O>,_). \<O>) ` set ts\<^sub>s\<^sub>b') =
              \<Union>((\<lambda>(_,_, _, _,_, \<O>,_). \<O>) ` set ts\<^sub>s\<^sub>b) \<union> A - R"
	      
		apply (unfold ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b') 
		apply (rule acquire_release_ownership_nth_update [OF R_owned i_bound ts\<^sub>s\<^sub>b_i])
		apply (rule local.ownership_distinct_axioms)
		done
	      
	      note unowned_shared L_subset A_R
	      then
	      show ?thesis
		apply (simp only: s)
		apply auto
		done
	    qed
	  qed
	next
	  show "no_outstanding_write_to_read_only_memory (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	  proof 
	    fix j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j acq\<^sub>j xs\<^sub>j sb\<^sub>j
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	    assume jth: "ts\<^sub>s\<^sub>b' ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	    show "no_write_to_read_only_memory (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) sb\<^sub>j"
	    proof (cases "i=j")
	      case True
	      with jth ts\<^sub>s\<^sub>b_i i_bound no_outstanding_write_to_read_only_memory [OF i_bound ts\<^sub>s\<^sub>b_i]
	      show ?thesis
		by (auto simp add: sb ts\<^sub>s\<^sub>b' Write\<^sub>s\<^sub>b volatile)
	    next
	      case False
	      from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      with False jth have jth': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      from no_outstanding_write_to_read_only_memory [OF j_bound' jth']
	      have nw: "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b sb\<^sub>j".
	      have "R \<inter> outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>j = {}"
	      proof -
		note dist = ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth']
		from non_volatile_owned_or_read_only_outstanding_non_volatile_writes 
		[OF outstanding_non_volatile_refs_owned_or_read_only [OF j_bound' jth']]
		  dist
		have "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<inter> \<O>\<^sub>s\<^sub>b = {}"
		  by auto
		moreover
		from outstanding_volatile_writes_unowned_by_others [OF j_bound'  i_bound 
		  False [symmetric] jth' ts\<^sub>s\<^sub>b_i ]
		have "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<inter> \<O>\<^sub>s\<^sub>b = {}" 
		  by auto
		ultimately have "outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>j \<inter> \<O>\<^sub>s\<^sub>b = {}" 
		  by (auto simp add: misc_outstanding_refs_convs)
		with R_owned
		show ?thesis by blast
	      qed
	      then
	      have "\<forall>a\<in>outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>j.
		a \<in> read_only (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<longrightarrow> a \<in> read_only \<S>\<^sub>s\<^sub>b"
		by (auto simp add: in_read_only_convs) 
	      
	      from no_write_to_read_only_memory_read_only_reads_eq [OF nw this]
	      show ?thesis .
	    qed
	  qed
	qed
	 
	from direct_memop_step.WriteVolatile [OF]
	have "(Write True a (D, f) A L R W# is',
	  ?\<theta>, (), m,\<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b, release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b,\<S>) \<rightarrow> 
          (is', ?\<theta>, (), m (a := v),True, acquired True ?take_sb \<O>\<^sub>s\<^sub>b \<union> A - R, Map.empty,\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	  by (simp add: f_v' [symmetric])
	  
	from direct_computation.Memop [OF i_bound' ts_i this]
	have store_step: 
	  "(ts, m, \<S>) \<Rightarrow>\<^sub>d (?ts', m(a := v),\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".	

	have sb'_split: 
	  "sb' = takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb' @ 
                    dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb'"
	  by simp

	from reads_consis 
	have no_vol_reads: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb' = {}"
	  by (simp add: sb Write\<^sub>s\<^sub>b True)
	hence "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') 
	  = {}"
	  by (auto simp add: outstanding_refs_conv dest: set_takeWhileD)
	moreover 
	have "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b 
           (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') = {}"
	proof -
	  have "\<forall>r \<in> set (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb'). \<not> (is_volatile_Write\<^sub>s\<^sub>b r)"
	    by (auto dest: set_takeWhileD)
	  thus ?thesis
	    by (simp add: outstanding_refs_conv)
	qed
	ultimately
	have no_volatile: 
	  "outstanding_refs is_volatile (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') = {}"
	  by (auto simp add: outstanding_refs_conv is_volatile_split)

	moreover

	from no_vol_reads have "\<forall>r \<in> set sb'. \<not> is_volatile_Read\<^sub>s\<^sub>b r"
	  by (fastforce simp add: outstanding_refs_conv is_volatile_Read\<^sub>s\<^sub>b_def 
	    split: memref.splits)
	hence "\<forall>r \<in> set sb'. (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) r = (Not \<circ> is_volatile) r"
	  by (auto simp add: is_volatile_split)

	hence takeWhile_eq: "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') =
              (takeWhile (Not \<circ> is_volatile) sb')" 
	  apply -
	  apply (rule takeWhile_cong)
	  apply auto
	  done

	from leq
	have leq': "length ts\<^sub>s\<^sub>b = length ?ts'"
	  by simp
	hence i_bound_ts': "i < length ?ts'" using i_bound by simp

	from  is'_sim
	have is'_sim_split: 
	  "instrs 
                (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb' @ 
                 dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') @ is\<^sub>s\<^sub>b = 
              is' @ prog_instrs (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb' @ 
                                 dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')"
	  by (simp add: sb'_split [symmetric])

	from reads_consistent_flush_all_until_volatile_write [OF \<open>valid_ownership_and_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close>
	i_bound ts\<^sub>s\<^sub>b_i reads_consis]
	have "reads_consistent True (acquired True ?take_sb \<O>\<^sub>s\<^sub>b) m (Write\<^sub>s\<^sub>b True a (D,f) v A L R W#sb')"
	  by (simp add: m sb Write\<^sub>s\<^sub>b volatile)

	hence "reads_consistent True (acquired True ?take_sb \<O>\<^sub>s\<^sub>b \<union> A - R) (m(a:=v)) sb'"
	  by simp
	from reads_consistent_takeWhile [OF this]
	have r_consis': "reads_consistent True (acquired True ?take_sb \<O>\<^sub>s\<^sub>b \<union> A - R) (m(a:=v)) 
	       (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')".


	
	from last_prog have last_prog_sb': "last_prog p\<^sub>s\<^sub>b sb' = p\<^sub>s\<^sub>b"
	  by (simp add: sb Write\<^sub>s\<^sub>b )


	from valid_write_sops  [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "\<forall>sop \<in> write_sops sb'. valid_sop sop"
	  by (auto simp add: sb Write\<^sub>s\<^sub>b)
	hence valid_sop': "\<forall>sop\<in>write_sops (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb').
	        valid_sop sop"
	  by (fastforce dest: set_takeWhileD simp add: in_write_sops_conv)

	from no_volatile
	have no_volatile_Read\<^sub>s\<^sub>b:
	  "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') =
              {}"
	  by (auto simp add: outstanding_refs_conv is_volatile_Read\<^sub>s\<^sub>b_def split: memref.splits)
	from flush_store_buffer_append [OF i_bound_ts' is'_sim_split, simplified, 
	OF causal_program_history_sb' ts'_i refl last_prog_sb' r_consis' hist_consis' 
	  valid_sop' dist_sb' no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent [OF no_volatile_Read\<^sub>s\<^sub>b], 
	  where \<S>="(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"]

	  
	obtain is'' where
	  is''_sim: "instrs (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') @ is\<^sub>s\<^sub>b =
                      is'' @ prog_instrs (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')" and

          steps: "(?ts', m(a := v), \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<Rightarrow>\<^sub>d\<^sup>*
                   (ts[i := (last_prog (hd_prog p\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb'))
                            (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb'),
                         is'',
                         \<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b -
                                    read_tmps (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')),
                         (), True, acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')
                                (acquired True ?take_sb \<O>\<^sub>s\<^sub>b \<union> A - R),
                                release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')
                                   (dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) Map.empty)],
	           flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') (m(a := v)),
                   share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"


	  by (auto)

	note sim_flush = r_rtranclp_rtranclp [OF store_step steps]

	moreover
	note flush_commute =
	  flush_flush_all_until_volatile_write_Write\<^sub>s\<^sub>b_volatile_commute [OF i_bound ts\<^sub>s\<^sub>b_i [simplified sb Write\<^sub>s\<^sub>b True] 
	outstanding_refs_is_Write\<^sub>s\<^sub>b_takeWhile_disj a_notin_others']

	from last_prog_hd_prog_append' [where sb="(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')"
          and sb'="(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')",
	  simplified sb'_split [symmetric], OF hist_consis' last_prog_sb']
	have last_prog_eq: 
	  "last_prog (hd_prog p\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb'))
                 (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') =
              hd_prog p\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')".

	have take_emtpy: "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (r#sb) = []"
	  by (simp add: Write\<^sub>s\<^sub>b True)


        have dist_sb': "\<forall>i p is \<O> \<R> \<D> \<theta> sb.
          i < length ts\<^sub>s\<^sub>b \<longrightarrow>
          ts\<^sub>s\<^sub>b ! i = (p, is, \<theta>, sb, \<D>, \<O>, \<R>) \<longrightarrow>
          (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
          all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
          all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) \<inter>
          (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') \<union>
          all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') \<union>
          all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')) =
          {}"
        proof -
          {
            fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	    assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j, \<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	    assume x_shared: "x \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<union> 
                                 all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<union> 
                                 all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
            assume x_sb': "x \<in> (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') \<union>
                        all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') \<union>
                        all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb'))"
            have False
            proof (cases "i=j")
              case True with x_shared ts\<^sub>s\<^sub>b_i jth show False by (simp add: sb volatile Write\<^sub>s\<^sub>b)
            next
              case False
              from x_shared all_shared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]
                unshared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]
                all_shared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		"(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
                all_unshared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		"(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
                all_acquired_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
		"(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
              have "x \<in> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j "
                by auto
              moreover
              from x_sb' all_shared_acquired_or_owned [OF sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]]
                unshared_acquired_or_owned [OF sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]]
                all_shared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')" 
		"(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')"]
                all_unshared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')" 
		"(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')"]
                all_acquired_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')" 
		"(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')"]
              have "x \<in> all_acquired sb \<union> \<O>\<^sub>s\<^sub>b"
                by (auto simp add: sb Write\<^sub>s\<^sub>b volatile)
              moreover
              note ownership_distinct [OF i_bound j_bound False ts\<^sub>s\<^sub>b_i jth]
              ultimately show False by blast
            qed
          }
          thus ?thesis by blast
        qed

        have dist_R_L_A: "\<forall>j p is \<O> \<R> \<D> \<theta> sb.
          j < length ts\<^sub>s\<^sub>b \<longrightarrow> i\<noteq> j\<longrightarrow>
          ts\<^sub>s\<^sub>b ! j = (p, is, \<theta>, sb, \<D>, \<O>, \<R>) \<longrightarrow>
          (all_shared sb \<union> all_unshared sb \<union> all_acquired sb) \<inter> (R \<union> L \<union> A) = {}"
        proof -
          {
            fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	    assume j_bound: "j < length ts\<^sub>s\<^sub>b"
            assume neq_i_j: "i \<noteq> j"
	    assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j, \<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	    assume x_shared: "x \<in> all_shared sb\<^sub>j \<union> 
                                 all_unshared sb\<^sub>j \<union> 
                                 all_acquired  sb\<^sub>j"
            assume x_R_L_A: "x \<in> R \<union> L \<union> A"
            have False
            proof -
              from x_shared all_shared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]
                unshared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]

              have "x \<in> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j "
                by auto
              moreover
              from x_R_L_A R_owned L_subset
              have "x \<in> all_acquired sb \<union> \<O>\<^sub>s\<^sub>b"
                by (auto simp add: sb Write\<^sub>s\<^sub>b volatile)
              moreover
              note ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
              ultimately show False by blast
            qed
          }
          thus ?thesis by blast
        qed
        from local.ownership_distinct_axioms have "ownership_distinct ts\<^sub>s\<^sub>b" .
        from local.sharing_consis_axioms have "sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b".
        note share_commute=
          share_all_until_volatile_write_flush_commute [OF take_empty \<open>ownership_distinct ts\<^sub>s\<^sub>b\<close> \<open>sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> i_bound ts\<^sub>s\<^sub>b_i dist_sb' dist_R_L_A]
        
        have rel_commute_empty:
          "release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') (dom \<S> \<union> R - L) Map.empty =
                 release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') (dom \<S>\<^sub>s\<^sub>b \<union> R - L) Map.empty"
        proof -
          {
            fix a
            assume a_in: "a \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')"
            have "(a \<in> (dom \<S> \<union> R - L)) = (a \<in> (dom \<S>\<^sub>s\<^sub>b \<union> R - L))"
            proof -
              
              from all_shared_acquired_or_owned [OF sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]] a_in
                all_shared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')" "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')"]
              have "a \<in> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb  " 
                by (auto simp add: sb Write\<^sub>s\<^sub>b volatile)
              from share_all_until_volatile_write_thread_local [OF \<open>ownership_distinct ts\<^sub>s\<^sub>b\<close> \<open>sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> i_bound ts\<^sub>s\<^sub>b_i this]
              have "\<S> a = \<S>\<^sub>s\<^sub>b a"
                by (auto simp add: sb Write\<^sub>s\<^sub>b volatile \<S>)
              then show ?thesis
                by (auto simp add: domIff)
            qed
          }
          then show ?thesis
            apply -
            apply (rule release_all_shared_exchange)
            apply auto
            done
        qed
          
        {
	  fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	  assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b"
          assume neq: "i \<noteq> j" 
          have "release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)
                            (dom \<S>\<^sub>s\<^sub>b \<union> R - L) \<R>\<^sub>j
              = release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)
                            (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j"
          proof -
            {
              fix a
              assume a_in: "a \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
              have "(a \<in> (dom \<S>\<^sub>s\<^sub>b \<union> R - L)) = (a \<in> dom \<S>\<^sub>s\<^sub>b)"
              proof -
                from ownership_distinct [OF i_bound j_bound neq  ts\<^sub>s\<^sub>b_i jth]
                
                have A_dist: "A \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {}"
                  by (auto simp add: sb Write\<^sub>s\<^sub>b volatile)
              
                from  all_shared_acquired_or_owned [OF sharing_consis [OF j_bound jth]] a_in
                  all_shared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
                  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
                have a_in: "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
                  by auto
                with ownership_distinct [OF i_bound j_bound neq  ts\<^sub>s\<^sub>b_i jth]
                have "a \<notin> (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb)" by auto

              
                with A_dist R_owned A_R A_shared_owned L_subset a_in
                obtain "a \<notin> R" and "a \<notin> L"
                  by fastforce
                then show ?thesis by auto
              qed
            }
            then 
            show ?thesis 
              apply -
              apply (rule release_all_shared_exchange)
              apply auto
              done
          qed
        }
        note release_commute = this
	  
have "(ts\<^sub>s\<^sub>b [i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b, sb', \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b \<union> A - R,Map.empty)],m\<^sub>s\<^sub>b(a:=v),\<S>\<^sub>s\<^sub>b') \<sim> 
	      (ts[i := (last_prog (hd_prog p\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb'))
                            (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb'),
                         is'',
                         \<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b -
                                    read_tmps (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')),
                         (),True, acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')
                                (acquired True ?take_sb \<O>\<^sub>s\<^sub>b \<union> A - R),
                             release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')
                                   (dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) Map.empty)],
               flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') (m(a := v)),
               share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
	  apply (rule sim_config.intros) 
	  apply    (simp add: flush_commute m)
	  apply   (clarsimp simp add: \<S>\<^sub>s\<^sub>b' \<S> share_commute simp del: restrict_restrict)
	  using  leq
	  apply  simp
	  using i_bound i_bound' ts_sim \<D>
	  apply (clarsimp simp add: Let_def nth_list_update is''_sim last_prog_eq sb Write\<^sub>s\<^sub>b volatile  \<S>\<^sub>s\<^sub>b'
            rel_commute_empty
	     split: if_split_asm )
          apply (rule conjI)
          apply  blast
          apply clarsimp
          apply (frule (2) release_commute)
          apply clarsimp
          apply fastforce
	  done

	ultimately
	show ?thesis
	  using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' 
	   valid_dd' valid_sops' load_tmps_fresh' enough_flushs' 
	   valid_program_history' valid'
	    m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' 
	  by (auto simp del: fun_upd_apply simp add: \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' )

      next

	case False
	note non_vol = this
	
	from flush Write\<^sub>s\<^sub>b False
	obtain 
	  \<O>\<^sub>s\<^sub>b': "\<O>\<^sub>s\<^sub>b'=\<O>\<^sub>s\<^sub>b" and
	  \<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'=\<S>\<^sub>s\<^sub>b" and
          \<R>\<^sub>s\<^sub>b': "\<R>\<^sub>s\<^sub>b' = \<R>\<^sub>s\<^sub>b"
	  by cases (auto  simp add: sb)


	from non_volatile_owned non_vol have a_owned: "a \<in> \<O>\<^sub>s\<^sub>b"
	  by simp

	{
	  fix j 
	  fix p\<^sub>j is\<^sub>s\<^sub>b\<^sub>j \<O>\<^sub>j \<D>\<^sub>s\<^sub>b\<^sub>j \<theta>\<^sub>j \<R>\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b"
	  assume ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b!j=(p\<^sub>j,is\<^sub>s\<^sub>b\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>s\<^sub>b\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  assume neq_i_j: "i\<noteq>j"
	  have "a \<notin> unforwarded_non_volatile_reads (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) {}"
	  proof 
	    let ?take_sb\<^sub>j = "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j"
	    let ?drop_sb\<^sub>j = "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j"
	    assume a_in: "a \<in>  unforwarded_non_volatile_reads ?drop_sb\<^sub>j {}"
	    
	    from a_unowned_by_others [rule_format, OF j_bound neq_i_j] ts\<^sub>s\<^sub>b_j 
	    obtain a_unowned: "a \<notin> \<O>\<^sub>j" and a_unacq: "a \<notin> all_acquired sb\<^sub>j"
	      by auto
	    with all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j] acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b [of sb\<^sub>j \<O>\<^sub>j]
	    have a_unacq_take: "a \<notin> acquired True ?take_sb\<^sub>j \<O>\<^sub>j"
	      by (auto )

	    note nvo_j = outstanding_non_volatile_refs_owned_or_read_only [OF j_bound ts\<^sub>s\<^sub>b_j]
	  
	    from non_volatile_owned_or_read_only_drop [OF nvo_j]
	    have nvo_drop_j: "non_volatile_owned_or_read_only True (share ?take_sb\<^sub>j \<S>\<^sub>s\<^sub>b)
	      (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j" .
	    from in_unforwarded_non_volatile_reads_non_volatile_Read\<^sub>s\<^sub>b [OF a_in]
	    have a_in': "a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?drop_sb\<^sub>j".

	    from non_volatile_owned_or_read_only_outstanding_refs [OF nvo_drop_j] a_in'
	    have "a \<in> acquired True ?take_sb\<^sub>j \<O>\<^sub>j \<union> all_acquired ?drop_sb\<^sub>j \<union>  
	      read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
	      by (auto simp add: misc_outstanding_refs_convs)
	    
	    moreover 
	    from acquired_append [of True ?take_sb\<^sub>j ?drop_sb\<^sub>j \<O>\<^sub>j] acquired_all_acquired [of True ?take_sb\<^sub>j \<O>\<^sub>j]
	      all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	    have "acquired True ?take_sb\<^sub>j \<O>\<^sub>j \<union> all_acquired ?drop_sb\<^sub>j \<subseteq> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	      by auto
	    ultimately 
	    have "a \<in> read_only_reads (acquired True ?take_sb\<^sub>j \<O>\<^sub>j) ?drop_sb\<^sub>j"
	      using a_owned ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i ts\<^sub>s\<^sub>b_j]
	      by auto
	    
	    with read_only_reads_unowned [OF j_bound i_bound neq_i_j [symmetric] ts\<^sub>s\<^sub>b_j ts\<^sub>s\<^sub>b_i] a_owned
	    show False
	      by auto
	  qed
	} note a_notin_unforwarded_non_volatile_reads_drop = this
	    

	(* FIXME: the same proof as in volatile, case. depends on a_notin_unforwarded_non_volatile_reads_drop *)
	have valid_reads': "valid_reads m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)
	  fix j p\<^sub>j "is\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume ts_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b' sb\<^sub>j"
	  proof (cases "i=j")
	    case True
	    from reads_consis ts_j j_bound sb show ?thesis
	      by (clarsimp simp add: True  m\<^sub>s\<^sub>b' Write\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' False reads_consistent_pending_write_antimono)
	  next
	    case False
	    from j_bound have j_bound':  "j < length ts\<^sub>s\<^sub>b"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    moreover from ts_j False have ts_j': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      using j_bound by (simp add: ts\<^sub>s\<^sub>b')
	    ultimately have consis_m: "reads_consistent False \<O>\<^sub>j m\<^sub>s\<^sub>b sb\<^sub>j"
	      by (rule valid_reads)
	    from a_unowned_by_others [rule_format, OF j_bound' False] ts_j'
	    have a_unowned:"a \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	      by simp

	    let ?take_sb\<^sub>j = "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j"
	    let ?drop_sb\<^sub>j = "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j"

	    from a_unowned acquired_reads_all_acquired [of True ?take_sb\<^sub>j \<O>\<^sub>j]
	    all_acquired_append [of ?take_sb\<^sub>j ?drop_sb\<^sub>j]
	    have a_not_acq_reads: "a \<notin> acquired_reads True ?take_sb\<^sub>j \<O>\<^sub>j"
	      by auto
	    moreover
	    
	    note a_unfw= a_notin_unforwarded_non_volatile_reads_drop [OF j_bound' ts_j' False]
	    ultimately
	    show ?thesis
	      using reads_consistent_mem_eq_on_unforwarded_non_volatile_reads_drop [where W="{}" and 
		A="unforwarded_non_volatile_reads ?drop_sb\<^sub>j {} \<union> acquired_reads True ?take_sb\<^sub>j \<O>\<^sub>j" and
		m'= "(m\<^sub>s\<^sub>b(a:=v))", OF _ _ _ consis_m]
	      by (fastforce simp add: m\<^sub>s\<^sub>b')
	  qed
	qed

	have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof (intro_locales)
	  show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  proof -
	    from outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i] sb
	    have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb'"
	      by (auto simp add: Write\<^sub>s\<^sub>b False)
	    from outstanding_non_volatile_refs_owned_or_read_only_nth_update [OF i_bound this]
	    show ?thesis by (simp add: ts\<^sub>s\<^sub>b' Write\<^sub>s\<^sub>b False \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	  qed
	next
	  show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'"
	  proof -
	    from sb 
	    have out: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb' \<subseteq> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb"
	      by (auto simp add: Write\<^sub>s\<^sub>b False)
	    have acq: "all_acquired sb' \<subseteq> all_acquired sb"
	      by (auto simp add: Write\<^sub>s\<^sub>b False sb)
	    from outstanding_volatile_writes_unowned_by_others_store_buffer 
	    [OF i_bound ts\<^sub>s\<^sub>b_i out acq]
	    show ?thesis by (simp add: ts\<^sub>s\<^sub>b' Write\<^sub>s\<^sub>b False \<O>\<^sub>s\<^sub>b')
	  qed
	next
	  show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
	  proof -
	    have ro: "read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') \<O>\<^sub>s\<^sub>b)
	      (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')
	      \<subseteq> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>\<^sub>s\<^sub>b)
	      (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
	      by (auto simp add: sb Write\<^sub>s\<^sub>b non_vol)
	    have "\<O>\<^sub>s\<^sub>b \<union> all_acquired sb' \<subseteq> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
	      by (auto simp add: sb Write\<^sub>s\<^sub>b non_vol)
	    from read_only_reads_unowned_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i ro this] 
	    show ?thesis
	      by (simp add: ts\<^sub>s\<^sub>b' sb \<O>\<^sub>s\<^sub>b')
	  qed
	next
	  show "ownership_distinct ts\<^sub>s\<^sub>b'"
	  proof -
	    have acq: "all_acquired sb' \<subseteq> all_acquired sb"
	      by (auto simp add: Write\<^sub>s\<^sub>b False sb)
	    with ownership_distinct_instructions_read_value_store_buffer_independent 
	    [OF i_bound ts\<^sub>s\<^sub>b_i]
	    show ?thesis by (simp add: ts\<^sub>s\<^sub>b' Write\<^sub>s\<^sub>b False \<O>\<^sub>s\<^sub>b')
	  qed
	qed

	have valid_sharing': "valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof (intro_locales)	
	  from outstanding_non_volatile_writes_unshared [OF i_bound ts\<^sub>s\<^sub>b_i]
	  have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b sb'"
	    by (auto simp add: sb Write\<^sub>s\<^sub>b False)
	  from outstanding_non_volatile_writes_unshared_nth_update [OF i_bound this]
	  show "outstanding_non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	    by (simp add: ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	next
	  from sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]
	  have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb'"
	    by (auto simp add: sb Write\<^sub>s\<^sub>b False)
	  from sharing_consis_nth_update [OF i_bound this]
	  show "sharing_consis \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	    by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	next
	  from read_only_unowned_nth_update [OF i_bound read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] ]
	  show "read_only_unowned \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	    by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b')
	next
	  from unowned_shared_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i subset_refl]
	  show "unowned_shared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	    by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	next
	  from no_outstanding_write_to_read_only_memory [OF i_bound ts\<^sub>s\<^sub>b_i] 
	  have "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b sb'"
	    by (auto simp add: sb Write\<^sub>s\<^sub>b False)
	  from no_outstanding_write_to_read_only_memory_nth_update [OF i_bound this]
	  show "no_outstanding_write_to_read_only_memory \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	    by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb)
	qed

	from is_sim
	obtain is_sim: "instrs (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') @ is\<^sub>s\<^sub>b =
                 is @ prog_instrs (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')"
	  by (simp add: suspends sb Write\<^sub>s\<^sub>b False)

	have "(ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts,m,\<S>)" by blast

	moreover


	note flush_commute =
	  flush_all_until_volatile_write_Write\<^sub>s\<^sub>b_non_volatile_commute [OF i_bound ts\<^sub>s\<^sub>b_i [simplified sb Write\<^sub>s\<^sub>b non_vol] 
	outstanding_refs_is_Write\<^sub>s\<^sub>b_takeWhile_disj a_notin_others']

	note share_commute = 
	  share_all_until_volatile_write_update_sb [of sb' sb, OF _ i_bound ts\<^sub>s\<^sub>b_i, simplified sb Write\<^sub>s\<^sub>b False, simplified]
	have "(ts\<^sub>s\<^sub>b [i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b,\<theta>\<^sub>s\<^sub>b, sb', \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b)], m\<^sub>s\<^sub>b(a:=v),\<S>\<^sub>s\<^sub>b') \<sim> 
                (ts,m,\<S>)"
	  apply (rule sim_config.intros) 
	  apply    (simp add: m flush_commute)
	  apply   (clarsimp simp add: \<S> \<S>\<^sub>s\<^sub>b' share_commute)
	  using  leq
	  apply  simp
	  using i_bound i_bound' is_sim ts_i ts_sim \<D> 
	  apply (clarsimp simp add: Let_def nth_list_update suspends sb Write\<^sub>s\<^sub>b False \<S>\<^sub>s\<^sub>b'
	     split: if_split_asm )
	  done	

	ultimately
	show ?thesis
	  using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' m\<^sub>s\<^sub>b'
	   valid_dd' valid_sops' load_tmps_fresh' enough_flushs' valid_program_history' valid'
	    ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b'
	  by (auto simp del: fun_upd_apply)
      qed
    next
      case (Read\<^sub>s\<^sub>b volatile a t v)
      from flush this obtain m\<^sub>s\<^sub>b': "m\<^sub>s\<^sub>b'=m\<^sub>s\<^sub>b" and 
	\<O>\<^sub>s\<^sub>b': "\<O>\<^sub>s\<^sub>b'=\<O>\<^sub>s\<^sub>b" and \<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'=\<S>\<^sub>s\<^sub>b" and
        \<R>\<^sub>s\<^sub>b': "\<R>\<^sub>s\<^sub>b'=\<R>\<^sub>s\<^sub>b"
	by cases (auto simp add: sb)

      have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof -
	  from outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i] sb
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb'"
	    by (auto simp add: Read\<^sub>s\<^sub>b)
	  from outstanding_non_volatile_refs_owned_or_read_only_nth_update [OF i_bound this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' Read\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	qed
      next
	show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'"
	proof -
	  from sb 
	  have out: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb' \<subseteq> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb"
	    by (auto simp add: Read\<^sub>s\<^sub>b)
	  have acq: "all_acquired sb' \<subseteq> all_acquired sb"
	    by (auto simp add: Read\<^sub>s\<^sub>b sb)
	  from outstanding_volatile_writes_unowned_by_others_store_buffer 
	  [OF i_bound ts\<^sub>s\<^sub>b_i out acq]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' Read\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b')
	qed
      next
	show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
	proof -
	  have ro: "read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') \<O>\<^sub>s\<^sub>b)
	    (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')
	    \<subseteq> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>\<^sub>s\<^sub>b)
	    (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
	    by (auto simp add: sb Read\<^sub>s\<^sub>b)
	  have "\<O>\<^sub>s\<^sub>b \<union> all_acquired sb' \<subseteq> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
	    by (auto simp add: sb Read\<^sub>s\<^sub>b)
	  from read_only_reads_unowned_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i ro this] 
	  show ?thesis
	    by (simp add: ts\<^sub>s\<^sub>b' sb \<O>\<^sub>s\<^sub>b')
	qed
      next
	show "ownership_distinct ts\<^sub>s\<^sub>b'"
	proof -
	  have acq: "all_acquired sb' \<subseteq> all_acquired sb"
	    by (auto simp add: Read\<^sub>s\<^sub>b sb)
	  with ownership_distinct_instructions_read_value_store_buffer_independent 
	  [OF i_bound ts\<^sub>s\<^sub>b_i]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' Read\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b')
	qed
      qed

      have valid_sharing': "valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)	
	from outstanding_non_volatile_writes_unshared [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b sb'"
	  by (auto simp add: sb Read\<^sub>s\<^sub>b)
	from outstanding_non_volatile_writes_unshared_nth_update [OF i_bound this]
	show "outstanding_non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next
	from sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb'"
	  by (auto simp add: sb Read\<^sub>s\<^sub>b)
	from sharing_consis_nth_update [OF i_bound this]
	show "sharing_consis \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next
	from read_only_unowned_nth_update [OF i_bound read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] ]
	show "read_only_unowned \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b')
      next
	from unowned_shared_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i subset_refl]
	show "unowned_shared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next
	from no_outstanding_write_to_read_only_memory [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b sb'"
	  by (auto simp add: sb Read\<^sub>s\<^sub>b)
	from no_outstanding_write_to_read_only_memory_nth_update [OF i_bound this]
	show "no_outstanding_write_to_read_only_memory \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb)
      qed	

      have valid_reads': "valid_reads m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof -
	from valid_reads [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b sb'"
	  by (simp add: sb Read\<^sub>s\<^sub>b)
	from valid_reads_nth_update [OF i_bound this]
	show ?thesis by (simp add: m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b')
      qed

      have valid_program_history': "valid_program_history ts\<^sub>s\<^sub>b'"
      proof -	
	from valid_program_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "causal_program_history is\<^sub>s\<^sub>b sb" .
	then have causal': "causal_program_history is\<^sub>s\<^sub>b sb'"
	  by (simp add: sb Read\<^sub>s\<^sub>b causal_program_history_def)

	from valid_last_prog [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "last_prog p\<^sub>s\<^sub>b sb = p\<^sub>s\<^sub>b".
	hence "last_prog p\<^sub>s\<^sub>b sb' = p\<^sub>s\<^sub>b"
	  by (simp add: sb Read\<^sub>s\<^sub>b)

	from valid_program_history_nth_update [OF i_bound causal' this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b')
      qed

      from is_sim
      have is_sim: "instrs (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') @ is\<^sub>s\<^sub>b =
	         is @ prog_instrs (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')"
	by (simp add: sb Read\<^sub>s\<^sub>b suspends)

      from valid_history [OF i_bound ts\<^sub>s\<^sub>b_i]
      have \<theta>\<^sub>s\<^sub>b_v: "\<theta>\<^sub>s\<^sub>b t = Some v"
	by (simp add: history_consistent_access_last_read sb Read\<^sub>s\<^sub>b split:option.splits)

      have "(ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts,m,\<S>)" by blast

      moreover

      note flush_commute= flush_all_until_volatile_write_Read\<^sub>s\<^sub>b_commute [OF i_bound ts\<^sub>s\<^sub>b_i [simplified sb Read\<^sub>s\<^sub>b]]
 
      note share_commute = 
	  share_all_until_volatile_write_update_sb [of sb' sb, OF _ i_bound ts\<^sub>s\<^sub>b_i, simplified sb Read\<^sub>s\<^sub>b, simplified]
      have "(ts\<^sub>s\<^sub>b [i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b, sb',\<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b')],m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> (ts,m,\<S>)"
	apply (rule sim_config.intros) 
	apply    (simp add: m flush_commute)
	apply   (clarsimp simp add: \<S> \<S>\<^sub>s\<^sub>b' share_commute)
	using  leq
	apply  simp
	
	using i_bound i_bound' ts_sim ts_i is_sim \<D>
	apply (clarsimp simp add: Let_def nth_list_update sb suspends Read\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b'
	   split: if_split_asm)
	done	

      ultimately show ?thesis
	using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' m\<^sub>s\<^sub>b'
	  valid_dd' valid_sops' load_tmps_fresh' enough_flushs' valid_sharing' 
	  valid_program_history' valid'
	  ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' 
	by (auto simp del: fun_upd_apply)
    next
      case (Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis)
      from flush this obtain m\<^sub>s\<^sub>b': "m\<^sub>s\<^sub>b'=m\<^sub>s\<^sub>b" and 
	\<O>\<^sub>s\<^sub>b': "\<O>\<^sub>s\<^sub>b'=\<O>\<^sub>s\<^sub>b" and \<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'=\<S>\<^sub>s\<^sub>b" and
        \<R>\<^sub>s\<^sub>b': "\<R>\<^sub>s\<^sub>b'=\<R>\<^sub>s\<^sub>b"
	by cases (auto simp add: sb)

      have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof -
	  from outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i] sb
	  have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb'"
	    by (auto simp add: Prog\<^sub>s\<^sub>b)
	  from outstanding_non_volatile_refs_owned_or_read_only_nth_update [OF i_bound this]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' Prog\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
	qed
      next
	show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'"
	proof -
	  from sb 
	  have out: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb' \<subseteq> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb"
	    by (auto simp add: Prog\<^sub>s\<^sub>b)
	  have acq: "all_acquired sb' \<subseteq> all_acquired sb"
	    by (auto simp add: Prog\<^sub>s\<^sub>b sb)
	  from outstanding_volatile_writes_unowned_by_others_store_buffer 
	  [OF i_bound ts\<^sub>s\<^sub>b_i out acq]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' Prog\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b')
	qed
      next
	show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
	proof -
	  have ro: "read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') \<O>\<^sub>s\<^sub>b)
	    (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')
	      \<subseteq> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>\<^sub>s\<^sub>b)
	    (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
	    by (auto simp add: sb Prog\<^sub>s\<^sub>b)
	  have "\<O>\<^sub>s\<^sub>b \<union> all_acquired sb' \<subseteq> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
	    by (auto simp add: sb Prog\<^sub>s\<^sub>b)
	  from read_only_reads_unowned_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i ro this] 
	  show ?thesis
	    by (simp add: ts\<^sub>s\<^sub>b' sb \<O>\<^sub>s\<^sub>b')
	qed
      next
	  show "ownership_distinct ts\<^sub>s\<^sub>b'"
	  proof -
	  have acq: "all_acquired sb' \<subseteq> all_acquired sb"
	    by (auto simp add: Prog\<^sub>s\<^sub>b sb)
	  with ownership_distinct_instructions_read_value_store_buffer_independent 
	  [OF i_bound ts\<^sub>s\<^sub>b_i]
	  show ?thesis by (simp add: ts\<^sub>s\<^sub>b' Prog\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b')
	qed
      qed

      have valid_sharing': "valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)	
	from outstanding_non_volatile_writes_unshared [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b sb'"
	  by (auto simp add: sb Prog\<^sub>s\<^sub>b)
	from outstanding_non_volatile_writes_unshared_nth_update [OF i_bound this]
	show "outstanding_non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next
	from sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b sb'"
	  by (auto simp add: sb Prog\<^sub>s\<^sub>b)
	from sharing_consis_nth_update [OF i_bound this]
	show "sharing_consis \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next
	from read_only_unowned_nth_update [OF i_bound read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] ]
	show "read_only_unowned \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b')
      next
	from unowned_shared_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i subset_refl]
	show "unowned_shared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      next
	from no_outstanding_write_to_read_only_memory [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b sb'"
	  by (auto simp add: sb Prog\<^sub>s\<^sub>b)
	from no_outstanding_write_to_read_only_memory_nth_update [OF i_bound this]
	show "no_outstanding_write_to_read_only_memory \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	  by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' sb)
      qed
      
      have valid_reads': "valid_reads m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof -
	from valid_reads [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b sb'"
	  by (simp add: sb Prog\<^sub>s\<^sub>b)
	from valid_reads_nth_update [OF i_bound this]
	show ?thesis by (simp add: m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b')
      qed

      have valid_program_history': "valid_program_history ts\<^sub>s\<^sub>b'"
      proof -	
	from valid_program_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "causal_program_history is\<^sub>s\<^sub>b sb" .
	then have causal': "causal_program_history is\<^sub>s\<^sub>b sb'"
	  by (simp add: sb Prog\<^sub>s\<^sub>b causal_program_history_def)

	from valid_last_prog [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "last_prog p\<^sub>s\<^sub>b sb = p\<^sub>s\<^sub>b".
	hence "last_prog p\<^sub>2 sb' = p\<^sub>s\<^sub>b"
	  by (simp add: sb Prog\<^sub>s\<^sub>b)
	from last_prog_to_last_prog_same [OF this]
	have "last_prog p\<^sub>s\<^sub>b sb' = p\<^sub>s\<^sub>b".

	from valid_program_history_nth_update [OF i_bound causal' this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b')
      qed

      from is_sim
      have is_sim: "instrs (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') @ is\<^sub>s\<^sub>b =
	is @ prog_instrs (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')"
	by (simp add: suspends sb Prog\<^sub>s\<^sub>b)

      have "(ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts,m,\<S>)" by blast

      moreover

      note flush_commute = flush_all_until_volatile_write_Prog\<^sub>s\<^sub>b_commute [OF i_bound 
	ts\<^sub>s\<^sub>b_i [simplified sb Prog\<^sub>s\<^sub>b]]

      note share_commute = 
	  share_all_until_volatile_write_update_sb [of sb' sb, OF _ i_bound ts\<^sub>s\<^sub>b_i, simplified sb Prog\<^sub>s\<^sub>b, simplified]

      have "(ts\<^sub>s\<^sub>b [i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b, sb',\<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b)],m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> (ts,m,\<S>)"
	apply (rule sim_config.intros) 
	apply    (simp add: m flush_commute)
	apply   (clarsimp simp add: \<S> \<S>\<^sub>s\<^sub>b' share_commute)
	using  leq
	apply  simp
	
	using i_bound i_bound' ts_sim ts_i is_sim \<D>
	apply (clarsimp simp add: Let_def nth_list_update sb suspends Prog\<^sub>s\<^sub>b \<R>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b'
	   split: if_split_asm)
	done	
      ultimately show ?thesis
	using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' m\<^sub>s\<^sub>b'
	  valid_dd' valid_sops' load_tmps_fresh' enough_flushs' valid_sharing' 
	  valid_program_history' valid' 
	  ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b'
	by (auto simp del: fun_upd_apply)
    next
      case (Ghost\<^sub>s\<^sub>b A L R W)
      from flush Ghost\<^sub>s\<^sub>b
      obtain 
	\<O>\<^sub>s\<^sub>b': "\<O>\<^sub>s\<^sub>b'=\<O>\<^sub>s\<^sub>b \<union> A - R" and
	\<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'=\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and
        \<R>\<^sub>s\<^sub>b': "\<R>\<^sub>s\<^sub>b'= augment_rels (dom \<S>\<^sub>s\<^sub>b) R \<R>\<^sub>s\<^sub>b" and
	m\<^sub>s\<^sub>b': "m\<^sub>s\<^sub>b'=m\<^sub>s\<^sub>b" 
	by cases (auto simp add: sb)

      from sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i] 
      obtain 
	A_shared_owned: "A \<subseteq> dom \<S>\<^sub>s\<^sub>b \<union> \<O>\<^sub>s\<^sub>b" and
	L_subset: "L \<subseteq> A" and
	A_R: "A \<inter> R = {}" and
	R_owned: "R \<subseteq> \<O>\<^sub>s\<^sub>b"
	by (clarsimp simp add: sb Ghost\<^sub>s\<^sub>b)

      have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	proof 
	  fix j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j acq\<^sub>j \<theta>\<^sub>j sb\<^sub>j p\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume ts\<^sub>s\<^sub>b'_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b' \<O>\<^sub>j sb\<^sub>j"
	  proof (cases "j=i")
	    case True
	    from outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i]
	    have "non_volatile_owned_or_read_only False (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O>\<^sub>s\<^sub>b \<union> A - R) sb'"
	      by (auto simp add: sb Ghost\<^sub>s\<^sub>b non_volatile_owned_or_read_only_pending_write_antimono)
	    then show ?thesis
	      using True i_bound ts\<^sub>s\<^sub>b'_j
	      by (auto simp add: ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' sb \<O>\<^sub>s\<^sub>b')
	  next
	    case False
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    with ts\<^sub>s\<^sub>b'_j False i_bound 
	    have ts\<^sub>s\<^sub>b_j: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	      
	      
	    note nvo = outstanding_non_volatile_refs_owned_or_read_only [OF j_bound' ts\<^sub>s\<^sub>b_j]

	    from read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] R_owned
	    have "R \<inter> read_only \<S>\<^sub>s\<^sub>b = {}"
	      by auto

	    with read_only_reads_unowned [OF j_bound' i_bound False ts\<^sub>s\<^sub>b_j ts\<^sub>s\<^sub>b_i] L_subset
	    have "\<forall>a\<in>read_only_reads
	      (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j)
		(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j).
		a \<in> read_only \<S>\<^sub>s\<^sub>b \<longrightarrow> a \<in> read_only (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L )"
	      by (auto simp add: in_read_only_convs sb Ghost\<^sub>s\<^sub>b)
	    from non_volatile_owned_or_read_only_read_only_reads_eq' [OF nvo this]
	    have "non_volatile_owned_or_read_only False (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<O>\<^sub>j sb\<^sub>j".
	    thus ?thesis by (simp add: \<S>\<^sub>s\<^sub>b')
	  qed
	qed
      next
	show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)
	  fix i\<^sub>1 j p\<^sub>1 "is\<^sub>1" \<O>\<^sub>1 \<R>\<^sub>1 \<D>\<^sub>1 xs\<^sub>1 sb\<^sub>1 p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume i\<^sub>1_bound: "i\<^sub>1 < length ts\<^sub>s\<^sub>b'"
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume i\<^sub>1_j: "i\<^sub>1 \<noteq> j"
	  assume ts_i\<^sub>1: "ts\<^sub>s\<^sub>b'!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	  assume ts_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}"
	  proof (cases "i\<^sub>1=i")
	    case True
	    from i\<^sub>1_j True have neq_i_j: "i\<noteq>j"
	      by auto
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    from ts_j neq_i_j have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    from outstanding_volatile_writes_unowned_by_others [OF i_bound j_bound' neq_i_j
	      ts\<^sub>s\<^sub>b_i ts_j'] ts_i\<^sub>1 i_bound ts\<^sub>s\<^sub>b_i True show ?thesis
	      by (clarsimp simp add: ts\<^sub>s\<^sub>b' sb Ghost\<^sub>s\<^sub>b)
	  next
	    case False
	    note i\<^sub>1_i = this
	    from i\<^sub>1_bound have i\<^sub>1_bound': "i\<^sub>1 < length ts\<^sub>s\<^sub>b"
	      by (simp add: ts\<^sub>s\<^sub>b' sb)
	    hence i\<^sub>1_bound'': "i\<^sub>1 < length (map owned ts\<^sub>s\<^sub>b)"
	      by auto
	    from ts_i\<^sub>1 False have ts_i\<^sub>1': "ts\<^sub>s\<^sub>b!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	      by (simp add: ts\<^sub>s\<^sub>b' sb)
	    show ?thesis
	    proof (cases "j=i")
	      case True
	      from outstanding_volatile_writes_unowned_by_others [OF i\<^sub>1_bound' i_bound  i\<^sub>1_i  ts_i\<^sub>1' ts\<^sub>s\<^sub>b_i ]
	      have "(\<O>\<^sub>s\<^sub>b \<union> all_acquired sb) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}".
	      then show ?thesis
		using True i\<^sub>1_i ts_j ts\<^sub>s\<^sub>b_i i_bound
		by (auto simp add: sb Ghost\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b')
	    next
	      case False
	      from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from ts_j False have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from outstanding_volatile_writes_unowned_by_others 
	      [OF i\<^sub>1_bound' j_bound' i\<^sub>1_j ts_i\<^sub>1' ts_j']
	      show "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>1 = {}" .
	    qed
	  qed
	qed
      next
	show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
	proof 
	  fix n m
	  fix p\<^sub>n "is\<^sub>n" \<O>\<^sub>n \<R>\<^sub>n \<D>\<^sub>n \<theta>\<^sub>n sb\<^sub>n p\<^sub>m "is\<^sub>m" \<O>\<^sub>m \<R>\<^sub>m \<D>\<^sub>m \<theta>\<^sub>m sb\<^sub>m
	  assume n_bound: "n < length ts\<^sub>s\<^sub>b'"
	    and m_bound: "m < length ts\<^sub>s\<^sub>b'"
	    and neq_n_m: "n\<noteq>m"
	    and nth: "ts\<^sub>s\<^sub>b'!n = (p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
	    and mth: "ts\<^sub>s\<^sub>b'!m =(p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m,\<R>\<^sub>m)"
	  from n_bound have n_bound': "n < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')
	  from m_bound have m_bound': "m < length ts\<^sub>s\<^sub>b" by (simp add: ts\<^sub>s\<^sub>b')
	  show "(\<O>\<^sub>m \<union> all_acquired sb\<^sub>m) \<inter>
            read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) \<O>\<^sub>n)
            (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) =
            {}"
	  proof (cases "m=i")
	    case True
	    with neq_n_m have neq_n_i: "n\<noteq>i"
	      by auto
	    
	    with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    note read_only_reads_unowned [OF n_bound' i_bound  neq_n_i nth' ts\<^sub>s\<^sub>b_i]
	    then
	    show ?thesis
	      using True ts\<^sub>s\<^sub>b_i neq_n_i nth mth n_bound' m_bound' L_subset
	      by (auto simp add: ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b' sb Ghost\<^sub>s\<^sub>b)
	  next
	    case False
	    note neq_m_i = this
	    with m_bound mth i_bound have mth': "ts\<^sub>s\<^sub>b!m = (p\<^sub>m, is\<^sub>m, \<theta>\<^sub>m, sb\<^sub>m, \<D>\<^sub>m, \<O>\<^sub>m,\<R>\<^sub>m)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    show ?thesis
	    proof (cases "n=i")
	      case True
	      from read_only_reads_append [of "(\<O>\<^sub>s\<^sub>b \<union> A - R)" "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n)"
		"(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n)"]
	      have "read_only_reads
                (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) (\<O>\<^sub>s\<^sub>b \<union> A - R))
                (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>n) \<subseteq> read_only_reads (\<O>\<^sub>s\<^sub>b \<union> A - R) sb\<^sub>n"
		by auto
		
	      with ts\<^sub>s\<^sub>b_i nth mth neq_m_i n_bound' True
		read_only_reads_unowned [OF i_bound m_bound' False [symmetric] ts\<^sub>s\<^sub>b_i mth']
	      show ?thesis
		by (auto simp add: ts\<^sub>s\<^sub>b'  sb \<O>\<^sub>s\<^sub>b' Ghost\<^sub>s\<^sub>b)
	    next
	      case False
	      with n_bound nth i_bound have nth': "ts\<^sub>s\<^sub>b!n =(p\<^sub>n, is\<^sub>n, \<theta>\<^sub>n, sb\<^sub>n, \<D>\<^sub>n, \<O>\<^sub>n,\<R>\<^sub>n)"
		by (auto simp add: ts\<^sub>s\<^sub>b')
	      from read_only_reads_unowned [OF n_bound' m_bound' neq_n_m  nth' mth'] False neq_m_i
	      show ?thesis 
		by (clarsimp)
	    qed
	  qed
	qed
      next
	show "ownership_distinct ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)
	  fix i\<^sub>1 j p\<^sub>1 "is\<^sub>1" \<O>\<^sub>1 \<R>\<^sub>1 \<D>\<^sub>1 xs\<^sub>1 sb\<^sub>1 p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume i\<^sub>1_bound: "i\<^sub>1 < length ts\<^sub>s\<^sub>b'"
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume i\<^sub>1_j: "i\<^sub>1 \<noteq> j"
	  assume ts_i\<^sub>1: "ts\<^sub>s\<^sub>b'!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	  assume ts_j: "ts\<^sub>s\<^sub>b'!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "(\<O>\<^sub>1 \<union> all_acquired sb\<^sub>1) \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j)= {}"
	  proof (cases "i\<^sub>1=i")
	    case True
	    with i\<^sub>1_j have i_j: "i\<noteq>j" 
	      by simp
	    
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    hence j_bound'': "j < length (map owned ts\<^sub>s\<^sub>b)"
	      by simp	    
	    from ts_j i_j have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    
	    from ownership_distinct [OF i_bound j_bound' i_j ts\<^sub>s\<^sub>b_i ts_j']
	    show ?thesis
	      using ts\<^sub>s\<^sub>b_i True ts_i\<^sub>1 i_bound \<O>\<^sub>s\<^sub>b'
	      by (auto simp add: ts\<^sub>s\<^sub>b' sb Ghost\<^sub>s\<^sub>b)
	  next
	    case False
	    note i\<^sub>1_i = this
	    from i\<^sub>1_bound have i\<^sub>1_bound': "i\<^sub>1 < length ts\<^sub>s\<^sub>b"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    hence i\<^sub>1_bound'': "i\<^sub>1 < length (map owned ts\<^sub>s\<^sub>b)"
	      by simp	    
	    from ts_i\<^sub>1 False have ts_i\<^sub>1': "ts\<^sub>s\<^sub>b!i\<^sub>1 = (p\<^sub>1,is\<^sub>1,xs\<^sub>1,sb\<^sub>1,\<D>\<^sub>1,\<O>\<^sub>1,\<R>\<^sub>1)"
	      by (simp add: ts\<^sub>s\<^sub>b')
	    show ?thesis
	    proof (cases "j=i")
	      case True
	      from ownership_distinct [OF i\<^sub>1_bound' i_bound  i\<^sub>1_i ts_i\<^sub>1' ts\<^sub>s\<^sub>b_i]
	      show ?thesis
		using ts\<^sub>s\<^sub>b_i True ts_j i_bound \<O>\<^sub>s\<^sub>b'
		by (auto simp add: ts\<^sub>s\<^sub>b' sb Ghost\<^sub>s\<^sub>b)
	    next
	      case False
	      from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from ts_j False have ts_j': "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
		by (simp add: ts\<^sub>s\<^sub>b')
	      from ownership_distinct [OF i\<^sub>1_bound' j_bound' i\<^sub>1_j ts_i\<^sub>1' ts_j']
	      show ?thesis .
	    qed
	  qed
	qed
      qed

      have valid_sharing': "valid_sharing (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
      proof (intro_locales)
	show "outstanding_non_volatile_writes_unshared (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)
	  fix j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j acq\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume jth: "ts\<^sub>s\<^sub>b' ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "non_volatile_writes_unshared (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)  sb\<^sub>j"
	  proof (cases "i=j")
	    case True
	    with outstanding_non_volatile_writes_unshared [OF i_bound ts\<^sub>s\<^sub>b_i]
	      i_bound jth ts\<^sub>s\<^sub>b_i show ?thesis
	      by (clarsimp simp add: ts\<^sub>s\<^sub>b' sb Ghost\<^sub>s\<^sub>b)
	  next
	    case False
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    from jth False have jth': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    from j_bound jth i_bound False
	    have j: "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b sb\<^sub>j"
	      apply -
	      apply (rule outstanding_non_volatile_writes_unshared)
	      apply (auto simp add: ts\<^sub>s\<^sub>b')
	      done
	    from jth False have jth': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    from outstanding_non_volatile_writes_unshared [OF j_bound' jth']
	    have unshared: "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b sb\<^sub>j".
	      
	    have "\<forall>a\<in>dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom \<S>\<^sub>s\<^sub>b. a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
	    proof -
	      {
		fix a 
		assume a_in: "a \<in> dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom \<S>\<^sub>s\<^sub>b"
		hence a_R: "a \<in> R"
		  by clarsimp
		assume a_in_j: "a \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
		have False
	        proof -
		  from non_volatile_owned_or_read_only_outstanding_non_volatile_writes [OF
		      outstanding_non_volatile_refs_owned_or_read_only [OF j_bound' jth']]
		      a_in_j
		  have "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
		    by auto

		  moreover
		  with ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth'] a_R R_owned
		  show False
		    by blast
		qed
	      }
	      thus ?thesis by blast
	    qed
		  
		

	    from non_volatile_writes_unshared_no_outstanding_non_volatile_Write\<^sub>s\<^sub>b 
	      [OF unshared this]
	    show ?thesis .
	  qed
	qed
      next
	show "sharing_consis (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)  
	  fix j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j acq\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume jth: "ts\<^sub>s\<^sub>b' ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "sharing_consistent (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<O>\<^sub>j sb\<^sub>j"
	  proof (cases "i=j")
	    case True
	    with i_bound jth ts\<^sub>s\<^sub>b_i sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]
	    show ?thesis
	      by (clarsimp simp add: ts\<^sub>s\<^sub>b' sb Ghost\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b')
	  next
	    case False
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    from jth False have jth': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    from sharing_consis [OF j_bound' jth']
	    have consis: "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>j sb\<^sub>j".
	    
	    have acq_cond: "all_acquired sb\<^sub>j \<inter> dom \<S>\<^sub>s\<^sub>b - dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	    proof -
	      {
		fix a
		assume a_acq: "a \<in> all_acquired sb\<^sub>j" 
		assume "a \<in> dom \<S>\<^sub>s\<^sub>b" 
		assume a_L: "a \<in> L"
		have False
		proof -
		  from ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth']
		  have "A \<inter> all_acquired sb\<^sub>j = {}"
		    by (auto simp add: sb Ghost\<^sub>s\<^sub>b)
		  with a_acq a_L L_subset
		  show False
		    by blast
		qed
	      }
	      thus ?thesis
		by auto
	    qed

	    have uns_cond: "all_unshared sb\<^sub>j \<inter> dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom \<S>\<^sub>s\<^sub>b = {}"
	    proof -
	      {
		fix a
		assume a_uns: "a \<in> all_unshared sb\<^sub>j" 
		assume "a \<notin> L" 
		assume a_R:  "a \<in> R"
		have False
	        proof -
		  from unshared_acquired_or_owned [OF consis] a_uns
		  have "a \<in> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j" by auto
		  with ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth']  R_owned a_R
		  show False
		    by blast
		  qed
	      }
	      thus ?thesis
	        by auto
	    qed
	      
	    from sharing_consistent_preservation [OF consis acq_cond uns_cond]
	    show ?thesis
	      by (simp add: ts\<^sub>s\<^sub>b')
	  qed
	qed
      next
	show "unowned_shared (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	proof (unfold_locales)
	  show "- \<Union>((\<lambda>(_,_, _, _,_, \<O>,_). \<O>) ` set ts\<^sub>s\<^sub>b') \<subseteq> dom (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	  proof -
	    
	    have s: "\<Union>((\<lambda>(_,_, _, _,_, \<O>,_). \<O>) ` set ts\<^sub>s\<^sub>b') =
              \<Union>((\<lambda>(_,_, _, _,_, \<O>,_). \<O>) ` set ts\<^sub>s\<^sub>b) \<union> A - R"
	      
	      apply (unfold ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b') 
	      apply (rule acquire_release_ownership_nth_update [OF R_owned i_bound ts\<^sub>s\<^sub>b_i])
	      apply (rule local.ownership_distinct_axioms)
	      done
	      
	    note unowned_shared L_subset A_R
	    then
	    show ?thesis
	      apply (simp only: s)
	      apply auto
	      done
	  qed
	qed
      next
	show "read_only_unowned (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	proof 
	  fix j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume jth: "ts\<^sub>s\<^sub>b' ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "\<O>\<^sub>j \<inter> read_only (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	  proof (cases "i=j")
	    case True
	    from read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] 
	    have "(\<O>\<^sub>s\<^sub>b \<union> A - R ) \<inter> read_only (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	      by (auto simp add: in_read_only_convs )
	    with jth ts\<^sub>s\<^sub>b_i i_bound True
	    show ?thesis
	      by (auto simp add: \<O>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b')
	  next
	    case False
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    with False jth have jth': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    from read_only_unowned [OF j_bound' jth']
	    have "\<O>\<^sub>j \<inter> read_only \<S>\<^sub>s\<^sub>b = {}".
	    moreover
	    from ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth'] R_owned
	    have "(\<O>\<^sub>s\<^sub>b \<union> A) \<inter> \<O>\<^sub>j = {}"
	      by (auto simp add: sb Ghost\<^sub>s\<^sub>b)
	    moreover note R_owned A_R
	    ultimately show ?thesis
	      by (fastforce simp add: in_read_only_convs split: if_split_asm)
	  qed
	qed
      next
	show "no_outstanding_write_to_read_only_memory (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) ts\<^sub>s\<^sub>b'"
	proof 
	  fix j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b'"
	  assume jth: "ts\<^sub>s\<^sub>b' ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  show "no_write_to_read_only_memory (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) sb\<^sub>j"
	  proof (cases "i=j")
	    case True
	    with jth ts\<^sub>s\<^sub>b_i i_bound no_outstanding_write_to_read_only_memory [OF i_bound ts\<^sub>s\<^sub>b_i]
	    show ?thesis
	      by (auto simp add: sb ts\<^sub>s\<^sub>b' Ghost\<^sub>s\<^sub>b)
	  next
	    case False
	    from j_bound have j_bound': "j < length ts\<^sub>s\<^sub>b"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    with False jth have jth': "ts\<^sub>s\<^sub>b ! j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	      by (auto simp add: ts\<^sub>s\<^sub>b')
	    from no_outstanding_write_to_read_only_memory [OF j_bound' jth']
	    have nw: "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b sb\<^sub>j".

	    have "R \<inter> outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>j = {}"
	    proof -
	      note dist = ownership_distinct [OF i_bound j_bound' False ts\<^sub>s\<^sub>b_i jth']
	      from non_volatile_owned_or_read_only_outstanding_non_volatile_writes 
	      [OF outstanding_non_volatile_refs_owned_or_read_only [OF j_bound' jth']]
		dist
	      have "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<inter> \<O>\<^sub>s\<^sub>b = {}"
	        by auto
	      moreover
	      from outstanding_volatile_writes_unowned_by_others [OF j_bound'  i_bound 
		False [symmetric] jth' ts\<^sub>s\<^sub>b_i ]
	      have "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<inter> \<O>\<^sub>s\<^sub>b = {}" 
	        by auto
	      ultimately have "outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>j \<inter> \<O>\<^sub>s\<^sub>b = {}" 
	        by (auto simp add: misc_outstanding_refs_convs)
	      with R_owned
	      show ?thesis by blast
	    qed
	    then
	    have "\<forall>a\<in>outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>j.
	      a \<in> read_only (\<S>\<^sub>s\<^sub>b \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<longrightarrow> a \<in> read_only \<S>\<^sub>s\<^sub>b"
	      by (auto simp add: in_read_only_convs) 
	    
	    from no_write_to_read_only_memory_read_only_reads_eq [OF nw this]
	    show ?thesis .
	  qed
	qed
      qed
      
      have valid_reads': "valid_reads m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof -
	from valid_reads [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "reads_consistent False (\<O>\<^sub>s\<^sub>b \<union> A - R) m\<^sub>s\<^sub>b sb'"
	  by (simp add: sb Ghost\<^sub>s\<^sub>b)
	from valid_reads_nth_update [OF i_bound this]
	show ?thesis by (simp add: m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<O>\<^sub>s\<^sub>b')
      qed
      
      have valid_program_history': "valid_program_history ts\<^sub>s\<^sub>b'"
      proof -	
	from valid_program_history [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "causal_program_history is\<^sub>s\<^sub>b sb" .
	then have causal': "causal_program_history is\<^sub>s\<^sub>b sb'"
	  by (simp add: sb Ghost\<^sub>s\<^sub>b causal_program_history_def)

	from valid_last_prog [OF i_bound ts\<^sub>s\<^sub>b_i]
	have "last_prog p\<^sub>s\<^sub>b sb = p\<^sub>s\<^sub>b".
	hence "last_prog p\<^sub>s\<^sub>b sb' = p\<^sub>s\<^sub>b"
	  by (simp add: sb Ghost\<^sub>s\<^sub>b)

	from valid_program_history_nth_update [OF i_bound causal' this]
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b')
      qed

      from is_sim
      have is_sim: "instrs (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') @ is\<^sub>s\<^sub>b =
	         is @ prog_instrs (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')"
	by (simp add: sb Ghost\<^sub>s\<^sub>b suspends)


      have "(ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts,m,\<S>)" by blast
      moreover

      note flush_commute =
	flush_all_until_volatile_write_Ghost\<^sub>s\<^sub>b_commute [OF i_bound ts\<^sub>s\<^sub>b_i [simplified sb Ghost\<^sub>s\<^sub>b]]

      have dist_R_L_A: "\<forall>j p is \<O> \<R> \<D> \<theta> sb.
        j < length ts\<^sub>s\<^sub>b \<longrightarrow> i\<noteq> j\<longrightarrow>
        ts\<^sub>s\<^sub>b ! j = (p, is, \<theta>, sb, \<D>, \<O>, \<R>) \<longrightarrow>
        (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union> 
         all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union> 
         all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) \<inter> (R \<union> L \<union> A) = {}"
      proof -
        {
          fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	  assume j_bound: "j < length ts\<^sub>s\<^sub>b"
          assume neq_i_j: "i \<noteq> j"
	  assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j, \<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	  assume x_shared: "x \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<union> 
                                 all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<union> 
                                 all_acquired  (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
          assume x_R_L_A: "x \<in> R \<union> L \<union> A"
          have False
          proof -
            from x_shared all_shared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]
              unshared_acquired_or_owned [OF sharing_consis [OF j_bound jth]]
              all_shared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
              all_unshared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
              all_acquired_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
            have "x \<in> all_acquired sb\<^sub>j \<union> \<O>\<^sub>j "
              by auto
            moreover
            from x_R_L_A R_owned L_subset
            have "x \<in> all_acquired sb \<union> \<O>\<^sub>s\<^sub>b"
              by (auto simp add: sb Ghost\<^sub>s\<^sub>b)
            moreover
            note ownership_distinct [OF i_bound j_bound neq_i_j ts\<^sub>s\<^sub>b_i jth]
            ultimately show False by blast
          qed
        }
        thus ?thesis by blast
      qed

      {
	fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	assume jth: "ts\<^sub>s\<^sub>b!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	assume j_bound: "j < length ts\<^sub>s\<^sub>b"
        assume neq: "i \<noteq> j" 
        have "release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)
                            (dom \<S>\<^sub>s\<^sub>b \<union> R - L) \<R>\<^sub>j
              = release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)
                            (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>j"
        proof -
          {
            fix a
            assume a_in: "a \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
            have "(a \<in> (dom \<S>\<^sub>s\<^sub>b \<union> R - L)) = (a \<in> dom \<S>\<^sub>s\<^sub>b)"
            proof -
              from ownership_distinct [OF i_bound j_bound neq  ts\<^sub>s\<^sub>b_i jth]
                
              have A_dist: "A \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {}"
                by (auto simp add: sb Ghost\<^sub>s\<^sub>b)
              
              from  all_shared_acquired_or_owned [OF sharing_consis [OF j_bound jth]] a_in
                all_shared_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
                "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"]
              have a_in: "a \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
                by auto
              with ownership_distinct [OF i_bound j_bound neq  ts\<^sub>s\<^sub>b_i jth]
              have "a \<notin> (\<O>\<^sub>s\<^sub>b \<union> all_acquired sb)" by auto

              
              with A_dist R_owned A_R A_shared_owned L_subset a_in
              obtain "a \<notin> R" and "a \<notin> L"
                by fastforce
              then show ?thesis by auto
            qed
          }
          then 
          show ?thesis 
            apply -
            apply (rule release_all_shared_exchange)
            apply auto
            done
        qed
      }
      note release_commute = this
	    from ownership_distinct_axioms have "ownership_distinct ts\<^sub>s\<^sub>b".
      from sharing_consis_axioms have "sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b".
      note share_commute = share_all_until_volatile_write_Ghost\<^sub>s\<^sub>b_commute [OF \<open>ownership_distinct ts\<^sub>s\<^sub>b\<close> 
	\<open>sharing_consis \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> i_bound ts\<^sub>s\<^sub>b_i [simplified sb Ghost\<^sub>s\<^sub>b] dist_R_L_A]
      
      have "(ts\<^sub>s\<^sub>b [i := (p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b, sb', \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b \<union> A - R,augment_rels (dom \<S>\<^sub>s\<^sub>b) R \<R>\<^sub>s\<^sub>b)],m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> (ts,m,\<S>)"
	apply (rule sim_config.intros) 
	apply    (simp add: m flush_commute)
	apply   (clarsimp simp add: \<S> \<S>\<^sub>s\<^sub>b' share_commute)
	using  leq
	apply  simp
	using i_bound i_bound' ts_sim ts_i is_sim \<D>
	apply (clarsimp simp add: Let_def nth_list_update sb suspends Ghost\<^sub>s\<^sub>b \<R>\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b'
	   split: if_split_asm)
        apply (rule conjI)
        apply  fastforce
        apply clarsimp
        apply (frule (2) release_commute)
        apply clarsimp
        apply auto
	done	
      ultimately
      show ?thesis
	using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' 
	  valid_dd' valid_sops' load_tmps_fresh' enough_flushs' 
	  valid_program_history' valid'
	  m\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' 
	by (auto simp del: fun_upd_apply simp add: \<O>\<^sub>s\<^sub>b' \<R>\<^sub>s\<^sub>b')
    qed
 next
    case (Program i p\<^sub>s\<^sub>b "is\<^sub>s\<^sub>b" \<theta>\<^sub>s\<^sub>b sb \<D>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b \<R>\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis)
    then obtain
      ts\<^sub>s\<^sub>b': "ts\<^sub>s\<^sub>b' = ts\<^sub>s\<^sub>b[i := (p\<^sub>s\<^sub>b', is\<^sub>s\<^sub>b@mis, \<theta>\<^sub>s\<^sub>b, sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis], \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b)]" and
      i_bound: "i < length ts\<^sub>s\<^sub>b" and
      ts\<^sub>s\<^sub>b_i: "ts\<^sub>s\<^sub>b ! i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b,\<theta>\<^sub>s\<^sub>b,sb, \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b)" and
      prog: "\<theta>\<^sub>s\<^sub>b\<turnstile> p\<^sub>s\<^sub>b \<rightarrow>\<^sub>p (p\<^sub>s\<^sub>b',mis)" and
      \<S>\<^sub>s\<^sub>b': "\<S>\<^sub>s\<^sub>b'=\<S>\<^sub>s\<^sub>b" and
      m\<^sub>s\<^sub>b': "m\<^sub>s\<^sub>b'=m\<^sub>s\<^sub>b"
      by auto

    from sim obtain 
      m: "m = flush_all_until_volatile_write ts\<^sub>s\<^sub>b m\<^sub>s\<^sub>b" and
      \<S>: "\<S> = share_all_until_volatile_write ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b" and
      leq: "length ts\<^sub>s\<^sub>b = length ts" and
      ts_sim: "\<forall>i<length ts\<^sub>s\<^sub>b.
           let (p, is\<^sub>s\<^sub>b, \<theta>, sb, \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b,\<R>) = ts\<^sub>s\<^sub>b ! i;
               suspends = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb
           in  \<exists>is \<D>. instrs suspends @ is\<^sub>s\<^sub>b = is @ prog_instrs suspends \<and> 
                          \<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {}) \<and>
               ts ! i =
                   (hd_prog p suspends, 
                    is,
                    \<theta> |` (dom \<theta> - read_tmps suspends), (),
                    \<D>, 
                    acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>\<^sub>s\<^sub>b,
                    release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) (dom \<S>\<^sub>s\<^sub>b) \<R>)"
      by cases blast

    from i_bound leq have i_bound': "i < length ts"
      by auto

    have split_sb: "sb = takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb @ dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb"
      (is "sb = ?take_sb@?drop_sb")
      by simp

    from ts_sim [rule_format, OF i_bound] ts\<^sub>s\<^sub>b_i obtain suspends "is" \<D> where
      suspends: "suspends = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb" and
      is_sim: "instrs suspends @ is\<^sub>s\<^sub>b = is @ prog_instrs suspends" and
      \<D>: "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {})" and
      ts_i: "ts ! i =
          (hd_prog p\<^sub>s\<^sub>b suspends, is,
           \<theta>\<^sub>s\<^sub>b |` (dom \<theta>\<^sub>s\<^sub>b - read_tmps suspends), (), \<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,
           release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
      by (auto simp add: Let_def)

    from prog_step_preserves_valid [OF i_bound ts\<^sub>s\<^sub>b_i prog valid]
    have valid': "valid ts\<^sub>s\<^sub>b'"
      by (simp add: ts\<^sub>s\<^sub>b')

    have valid_own': "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
    proof (intro_locales)
      show "outstanding_non_volatile_refs_owned_or_read_only \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
      proof -
	from outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts\<^sub>s\<^sub>b_i] 
	have "non_volatile_owned_or_read_only False \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])"
	  by (auto simp add: non_volatile_owned_or_read_only_append)
	from outstanding_non_volatile_refs_owned_or_read_only_nth_update [OF i_bound this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
      qed
    next
      show "outstanding_volatile_writes_unowned_by_others ts\<^sub>s\<^sub>b'"
      proof -
	have out: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis]) \<subseteq> 
	      outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb"
	  by (auto simp add: outstanding_refs_conv )
	from outstanding_volatile_writes_unowned_by_others_store_buffer 
	[OF i_bound ts\<^sub>s\<^sub>b_i this]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' all_acquired_append)
      qed
    next
      show "read_only_reads_unowned ts\<^sub>s\<^sub>b'"
      proof -
	have ro: "read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])) \<O>\<^sub>s\<^sub>b)
	  (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis]))
	  \<subseteq> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>\<^sub>s\<^sub>b)
	  (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
	  apply (case_tac "outstanding_refs (is_volatile_Write\<^sub>s\<^sub>b) sb = {}")
	  apply (simp_all add: outstanding_vol_write_take_drop_appends
	    acquired_append read_only_reads_append )
	  done
	have "\<O>\<^sub>s\<^sub>b \<union> all_acquired (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis]) \<subseteq> \<O>\<^sub>s\<^sub>b \<union> all_acquired sb"
	  by (auto simp add: all_acquired_append)
	from read_only_reads_unowned_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i ro this] 
	show ?thesis
	  by (simp add: ts\<^sub>s\<^sub>b' )
      qed
    next
      show "ownership_distinct ts\<^sub>s\<^sub>b'"
      proof -
	from ownership_distinct_instructions_read_value_store_buffer_independent 
	[OF i_bound ts\<^sub>s\<^sub>b_i, where sb'="(sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])"]
	show ?thesis by (simp add: ts\<^sub>s\<^sub>b' all_acquired_append)
      qed
    qed

    from valid_last_prog [OF i_bound ts\<^sub>s\<^sub>b_i]
    have last_prog: "last_prog p\<^sub>s\<^sub>b sb = p\<^sub>s\<^sub>b".
    
    have valid_hist': "valid_history program_step ts\<^sub>s\<^sub>b'"
    proof -
      from valid_history [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b sb) sb".
      from history_consistent_append_Prog\<^sub>s\<^sub>b [OF prog this last_prog]
      have hist_consis': "history_consistent \<theta>\<^sub>s\<^sub>b (hd_prog p\<^sub>s\<^sub>b' (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])) 
        (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])".
      from valid_history_nth_update [OF i_bound this]
      show ?thesis by (simp add: ts\<^sub>s\<^sub>b')
    qed


    have valid_reads': "valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b'"
    proof -
      from valid_reads [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b sb" .
      from reads_consistent_snoc_Prog\<^sub>s\<^sub>b [OF this] 
      have "reads_consistent False \<O>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b  (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])".
      from valid_reads_nth_update [OF i_bound this]
      show ?thesis by (simp add: ts\<^sub>s\<^sub>b')
    qed

    have valid_sharing': "valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
    proof (intro_locales)	
      from outstanding_non_volatile_writes_unshared [OF i_bound ts\<^sub>s\<^sub>b_i] 
      have "non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])"
	by (auto simp add: non_volatile_writes_unshared_append)
      from outstanding_non_volatile_writes_unshared_nth_update [OF i_bound this]
      show "outstanding_non_volatile_writes_unshared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	by (simp add: ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
    next
      from sharing_consis [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "sharing_consistent \<S>\<^sub>s\<^sub>b \<O>\<^sub>s\<^sub>b (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])"
	by (auto simp add: sharing_consistent_append)
      from sharing_consis_nth_update [OF i_bound this]
      show "sharing_consis \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	by (simp add: ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
    next
      from read_only_unowned_nth_update [OF i_bound read_only_unowned [OF i_bound ts\<^sub>s\<^sub>b_i] ]
      show "read_only_unowned \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b')
    next
      from unowned_shared_nth_update [OF i_bound ts\<^sub>s\<^sub>b_i subset_refl]
      show "unowned_shared \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	by (simp add: ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b')
    next
      from no_outstanding_write_to_read_only_memory [OF i_bound ts\<^sub>s\<^sub>b_i] 

      have "no_write_to_read_only_memory \<S>\<^sub>s\<^sub>b (sb @ [Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])"
	by (simp add: no_write_to_read_only_memory_append)
	
      from no_outstanding_write_to_read_only_memory_nth_update [OF i_bound this]
      show "no_outstanding_write_to_read_only_memory \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'"
	by (simp add: \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b')
    qed

    have tmps_distinct': "tmps_distinct ts\<^sub>s\<^sub>b'"
    proof (intro_locales)
      from load_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "distinct_load_tmps is\<^sub>s\<^sub>b".
      with distinct_load_tmps_prog_step [OF i_bound ts\<^sub>s\<^sub>b_i prog valid] 
      have "distinct_load_tmps (is\<^sub>s\<^sub>b@mis)" 
	by (auto simp add: distinct_load_tmps_append)
	
      from load_tmps_distinct_nth_update [OF i_bound this]
      show "load_tmps_distinct ts\<^sub>s\<^sub>b'"
	by (simp add: ts\<^sub>s\<^sub>b')
    next
      from read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "distinct_read_tmps (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])"
	by (simp add: distinct_read_tmps_append)
      from read_tmps_distinct_nth_update [OF i_bound this]
      show "read_tmps_distinct ts\<^sub>s\<^sub>b'"
	by (simp add: ts\<^sub>s\<^sub>b')
    next
      from load_tmps_read_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
	distinct_load_tmps_prog_step [OF i_bound ts\<^sub>s\<^sub>b_i prog valid] 
      have "load_tmps (is\<^sub>s\<^sub>b@mis) \<inter> read_tmps (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis]) = {}"
	by (auto simp add: read_tmps_append load_tmps_append)
      from load_tmps_read_tmps_distinct_nth_update [OF i_bound this]
      show "load_tmps_read_tmps_distinct ts\<^sub>s\<^sub>b'" by (simp add: ts\<^sub>s\<^sub>b')
    qed

    have valid_dd': "valid_data_dependency ts\<^sub>s\<^sub>b'"
    proof -
      from data_dependency_consistent_instrs [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "data_dependency_consistent_instrs (dom \<theta>\<^sub>s\<^sub>b) is\<^sub>s\<^sub>b".
      with valid_data_dependency_prog_step [OF i_bound ts\<^sub>s\<^sub>b_i prog valid]  
	   load_tmps_write_tmps_distinct [OF i_bound ts\<^sub>s\<^sub>b_i]
      obtain
	"data_dependency_consistent_instrs (dom \<theta>\<^sub>s\<^sub>b) (is\<^sub>s\<^sub>b@mis)"
	"load_tmps (is\<^sub>s\<^sub>b@mis) \<inter> \<Union>(fst ` write_sops (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis]))  = {}"
	by (force simp add: load_tmps_append data_dependency_consistent_instrs_append
	 write_sops_append)
      from valid_data_dependency_nth_update [OF i_bound this]
      show ?thesis
	by (simp add: ts\<^sub>s\<^sub>b')
    qed

    have load_tmps_fresh': "load_tmps_fresh ts\<^sub>s\<^sub>b'"
    proof -
      
      from load_tmps_fresh [OF i_bound ts\<^sub>s\<^sub>b_i] 
      load_tmps_fresh_prog_step [OF i_bound ts\<^sub>s\<^sub>b_i prog valid]
      have "load_tmps (is\<^sub>s\<^sub>b@mis) \<inter> dom \<theta>\<^sub>s\<^sub>b = {}"
	by (auto simp add: load_tmps_append)
      from load_tmps_fresh_nth_update [OF i_bound this]
      show ?thesis
	by (simp add:  ts\<^sub>s\<^sub>b')
    qed

    have enough_flushs': "enough_flushs ts\<^sub>s\<^sub>b'"
    proof -
      from clean_no_outstanding_volatile_Write\<^sub>s\<^sub>b [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "\<not> \<D>\<^sub>s\<^sub>b \<longrightarrow> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis]) = {}"
	by (auto simp add: outstanding_refs_append)

      from enough_flushs_nth_update [OF i_bound this]
      show ?thesis
	by (simp add: ts\<^sub>s\<^sub>b')
    qed

    have valid_sops': "valid_sops ts\<^sub>s\<^sub>b'"
    proof -
      from valid_store_sops [OF i_bound ts\<^sub>s\<^sub>b_i] valid_sops_prog_step [OF prog] 
	valid_implies_valid_prog[OF i_bound ts\<^sub>s\<^sub>b_i valid]
      have valid_store: "\<forall>sop\<in>store_sops (is\<^sub>s\<^sub>b@mis). valid_sop sop"
	by (auto simp add: store_sops_append)

      from valid_write_sops [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "\<forall>sop\<in>write_sops (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis]). valid_sop sop"
	by (auto simp add: write_sops_append)
      from     valid_sops_nth_update [OF i_bound this valid_store]
      show ?thesis
	by (simp add: ts\<^sub>s\<^sub>b')
    qed

    have valid_program_history':"valid_program_history ts\<^sub>s\<^sub>b'"
    proof -	
      from valid_program_history [OF i_bound ts\<^sub>s\<^sub>b_i]
      have "causal_program_history is\<^sub>s\<^sub>b sb" .
      from causal_program_history_Prog\<^sub>s\<^sub>b [OF this]
      have causal': "causal_program_history (is\<^sub>s\<^sub>b@mis) (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])".
      from last_prog_append_Prog\<^sub>s\<^sub>b
      have "last_prog p\<^sub>s\<^sub>b' (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis]) = p\<^sub>s\<^sub>b'".
      from valid_program_history_nth_update [OF i_bound causal' this]
      show ?thesis
	by (simp add: ts\<^sub>s\<^sub>b')
    qed

    show ?thesis
    proof (cases "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}")
      case True
      from True have flush_all: "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = sb"
	by (auto simp add: outstanding_refs_conv)
      
      from True have suspend_nothing: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = []"
	by (auto simp add: outstanding_refs_conv)

      hence suspends_empty: "suspends = []"
	by (simp add: suspends)

      from suspends_empty is_sim have "is": "is = is\<^sub>s\<^sub>b"
	by (simp)

      from ts_i have ts_i: "ts ! i = (p\<^sub>s\<^sub>b, is\<^sub>s\<^sub>b, \<theta>\<^sub>s\<^sub>b, (), 
	\<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)"
	by (simp add: suspends_empty "is")

      from direct_computation.Program [OF i_bound' ts_i prog]
      have "(ts,m,\<S>) \<Rightarrow>\<^sub>d (ts[i := (p\<^sub>s\<^sub>b', is\<^sub>s\<^sub>b @ mis, \<theta>\<^sub>s\<^sub>b, (),
	\<D>, acquired True ?take_sb \<O>\<^sub>s\<^sub>b,release ?take_sb (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b)], m, \<S>)".
    
      moreover

      note flush_commute = flush_all_until_volatile_write_append_Prog\<^sub>s\<^sub>b_commute [OF i_bound ts\<^sub>s\<^sub>b_i]

      from True
      have suspend_nothing':
	"(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])) = []"
	by (auto simp add: outstanding_refs_conv)

      note share_commute =
	share_all_until_volatile_write_update_sb [OF share_append_Prog\<^sub>s\<^sub>b i_bound ts\<^sub>s\<^sub>b_i]

      from \<D>
      have \<D>': "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis]) \<noteq>  {})"
	by (auto simp: outstanding_refs_append)

      have "(ts\<^sub>s\<^sub>b [i := (p\<^sub>s\<^sub>b',is\<^sub>s\<^sub>b@mis, \<theta>\<^sub>s\<^sub>b, sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis], \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b)],
              m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> 
              (ts[i:=(p\<^sub>s\<^sub>b', is\<^sub>s\<^sub>b @ mis, \<theta>\<^sub>s\<^sub>b, (), \<D>, 
                  acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) 
                    (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])) \<O>\<^sub>s\<^sub>b,
                   release (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])  (dom \<S>\<^sub>s\<^sub>b) \<R>\<^sub>s\<^sub>b )],m,\<S>)"
	apply (rule sim_config.intros) 
	apply    (simp add: m flush_commute)
	apply   (clarsimp simp add: \<S> \<S>\<^sub>s\<^sub>b' share_commute)
	using  leq
	apply  simp
	
	using i_bound i_bound' ts_sim ts_i \<D>'
	apply (clarsimp simp add: Let_def nth_list_update  flush_all suspend_nothing' Prog\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b' 
          release_append_Prog\<^sub>s\<^sub>b release_append
	   split: if_split_asm)
	done	
      ultimately show ?thesis
	using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' m\<^sub>s\<^sub>b'
	  valid_dd' valid_sops' load_tmps_fresh' enough_flushs' valid_sharing' 
	  valid_program_history' valid'  
	  \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'  
	by (auto simp del: fun_upd_apply simp add: acquired_append_Prog\<^sub>s\<^sub>b release_append_Prog\<^sub>s\<^sub>b release_append flush_all) 
    next
      case False

      then obtain r where r_in: "r \<in> set sb" and volatile_r: "is_volatile_Write\<^sub>s\<^sub>b r"
	by (auto simp add: outstanding_refs_conv)
      from takeWhile_dropWhile_real_prefix 
      [OF r_in, of  "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)", simplified, OF volatile_r] 
      obtain a' v' sb'' sop' A' L' R' W' where
	sb_split: "sb = takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb @ Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# sb''" 
	and
	drop: "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# sb''"
	apply (auto)
	subgoal for y
	apply (case_tac y)
	apply auto
	done
  done
      from drop suspends have suspends': "suspends = Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W'# sb''"
	by simp

      have "(ts, m, \<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts, m, \<S>)" by auto
      
      moreover

      note flush_commute= flush_all_until_volatile_write_append_Prog\<^sub>s\<^sub>b_commute [OF i_bound ts\<^sub>s\<^sub>b_i]

      have "Write\<^sub>s\<^sub>b True a' sop' v' A' L' R' W' \<in> set sb"
	by (subst sb_split) auto

      from dropWhile_append1 [OF this, of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)"]
      have drop_app_comm:
	  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis])) =
                dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb @ [Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis]"
	by simp

      note share_commute =
	share_all_until_volatile_write_update_sb [OF share_append_Prog\<^sub>s\<^sub>b i_bound ts\<^sub>s\<^sub>b_i]

      from \<D>
      have \<D>': "\<D>\<^sub>s\<^sub>b = (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis]) \<noteq>  {})"
	by (auto simp: outstanding_refs_append)
      have "(ts\<^sub>s\<^sub>b [i := (p\<^sub>s\<^sub>b',is\<^sub>s\<^sub>b@mis,\<theta>\<^sub>s\<^sub>b, sb@[Prog\<^sub>s\<^sub>b p\<^sub>s\<^sub>b p\<^sub>s\<^sub>b' mis], \<D>\<^sub>s\<^sub>b, \<O>\<^sub>s\<^sub>b,\<R>\<^sub>s\<^sub>b)],
              m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b') \<sim> 
              (ts,m,\<S>)"
	apply (rule sim_config.intros) 
	apply    (simp add: m flush_commute)
	apply   (clarsimp  simp add: \<S> \<S>\<^sub>s\<^sub>b' share_commute)
	using  leq
	apply  simp
	
	using i_bound i_bound' ts_sim ts_i is_sim suspends  suspends' [simplified suspends] \<D>'
	apply (clarsimp simp add: Let_def nth_list_update Prog\<^sub>s\<^sub>b
	  drop_app_comm instrs_append prog_instrs_append  
	  read_tmps_append hd_prog_append_Prog\<^sub>s\<^sub>b acquired_append_Prog\<^sub>s\<^sub>b release_append_Prog\<^sub>s\<^sub>b release_append \<S>\<^sub>s\<^sub>b'
	   split: if_split_asm)
	done	

      ultimately show ?thesis
	using valid_own' valid_hist' valid_reads' valid_sharing' tmps_distinct' m\<^sub>s\<^sub>b'
	  valid_dd' valid_sops' load_tmps_fresh' enough_flushs' valid_sharing' 
	  valid_program_history' valid'
	  \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' 
	by (auto simp del: fun_upd_apply)
    qed
  qed
qed


theorem (in xvalid_program) concurrent_direct_steps_simulates_store_buffer_history_steps:
  assumes step_sb: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b')"
  assumes valid_own: "valid_ownership \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b"
  assumes valid_sb_reads: "valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b"
  assumes valid_hist: "valid_history program_step ts\<^sub>s\<^sub>b"
  assumes valid_sharing: "valid_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b"
  assumes tmps_distinct: "tmps_distinct ts\<^sub>s\<^sub>b"
  assumes valid_sops: "valid_sops ts\<^sub>s\<^sub>b"
  assumes valid_dd: "valid_data_dependency ts\<^sub>s\<^sub>b"
  assumes load_tmps_fresh: "load_tmps_fresh ts\<^sub>s\<^sub>b"
  assumes enough_flushs: "enough_flushs ts\<^sub>s\<^sub>b"
  assumes valid_program_history: "valid_program_history ts\<^sub>s\<^sub>b"
  assumes valid: "valid ts\<^sub>s\<^sub>b"
  shows "\<And>ts \<S> m. (ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<sim> (ts,m,\<S>) \<Longrightarrow> safe_reach_direct safe_delayed (ts,m,\<S>) \<Longrightarrow>
         valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<and> valid_reads m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<and> valid_history program_step ts\<^sub>s\<^sub>b' \<and>
         valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b' \<and> tmps_distinct ts\<^sub>s\<^sub>b' \<and> valid_data_dependency ts\<^sub>s\<^sub>b' \<and>
         valid_sops ts\<^sub>s\<^sub>b' \<and> load_tmps_fresh ts\<^sub>s\<^sub>b' \<and> enough_flushs ts\<^sub>s\<^sub>b' \<and>
         valid_program_history ts\<^sub>s\<^sub>b' \<and> valid ts\<^sub>s\<^sub>b' \<and>
           (\<exists>ts' m' \<S>'. (ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>') \<and> (ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b') \<sim> (ts',m',\<S>'))"
using step_sb valid_own valid_sb_reads valid_hist valid_sharing tmps_distinct valid_sops 
  valid_dd load_tmps_fresh enough_flushs valid_program_history valid
proof (induct rule: converse_rtranclp_induct_sbh_steps)
  case refl thus ?case
    by auto
next
  case (step ts\<^sub>s\<^sub>b  m\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b''  m\<^sub>s\<^sub>b'' \<S>\<^sub>s\<^sub>b'')
  note first = \<open>(ts\<^sub>s\<^sub>b, m\<^sub>s\<^sub>b, \<S>\<^sub>s\<^sub>b) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h (ts\<^sub>s\<^sub>b'', m\<^sub>s\<^sub>b'', \<S>\<^sub>s\<^sub>b'')\<close>
  note sim = \<open>(ts\<^sub>s\<^sub>b, m\<^sub>s\<^sub>b, \<S>\<^sub>s\<^sub>b) \<sim> (ts, m, \<S>)\<close>
  note safe_reach = \<open>safe_reach_direct safe_delayed (ts, m, \<S>)\<close>
  note valid_own = \<open>valid_ownership \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close>
  note valid_reads = \<open>valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close>
  note valid_hist = \<open>valid_history program_step ts\<^sub>s\<^sub>b\<close>
  note valid_sharing = \<open>valid_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close>
  note tmps_distinct = \<open>tmps_distinct ts\<^sub>s\<^sub>b\<close>
  note valid_sops = \<open>valid_sops ts\<^sub>s\<^sub>b\<close>
  note valid_dd = \<open>valid_data_dependency ts\<^sub>s\<^sub>b\<close>
  note load_tmps_fresh = \<open>load_tmps_fresh ts\<^sub>s\<^sub>b\<close>
  note enough_flushs = \<open>enough_flushs ts\<^sub>s\<^sub>b\<close>
  note valid_prog_hist = \<open>valid_program_history ts\<^sub>s\<^sub>b\<close>
  note valid = \<open>valid ts\<^sub>s\<^sub>b\<close>
  from concurrent_direct_steps_simulates_store_buffer_history_step [OF first
  valid_own valid_reads valid_hist valid_sharing tmps_distinct valid_sops valid_dd
  load_tmps_fresh enough_flushs valid_prog_hist valid sim safe_reach]
  obtain ts'' m'' \<S>'' where
    valid_own'': "valid_ownership \<S>\<^sub>s\<^sub>b'' ts\<^sub>s\<^sub>b''" and
    valid_reads'': "valid_reads m\<^sub>s\<^sub>b'' ts\<^sub>s\<^sub>b''" and
    valid_hist'': "valid_history program_step ts\<^sub>s\<^sub>b''" and
    valid_sharing'': "valid_sharing \<S>\<^sub>s\<^sub>b'' ts\<^sub>s\<^sub>b''" and
    tmps_dist'': "tmps_distinct ts\<^sub>s\<^sub>b''" and
    valid_dd'': "valid_data_dependency ts\<^sub>s\<^sub>b''" and
    valid_sops'': "valid_sops ts\<^sub>s\<^sub>b''" and
    load_tmps_fresh'': "load_tmps_fresh ts\<^sub>s\<^sub>b''" and
    enough_flushs'': "enough_flushs ts\<^sub>s\<^sub>b''" and
    valid_prog_hist'': "valid_program_history ts\<^sub>s\<^sub>b''"and
    valid'': "valid ts\<^sub>s\<^sub>b''" and
    steps: "(ts, m, \<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts'', m'', \<S>'')" and
    sim: "(ts\<^sub>s\<^sub>b'', m\<^sub>s\<^sub>b'',\<S>\<^sub>s\<^sub>b'') \<sim> (ts'', m'',\<S>'')"
    by blast
 

  from step.hyps (3) [OF sim safe_reach_steps [OF safe_reach steps] valid_own'' valid_reads'' valid_hist'' valid_sharing''
  tmps_dist'' valid_sops'' valid_dd'' load_tmps_fresh'' enough_flushs'' valid_prog_hist'' valid'' ]

  obtain ts' m' \<S>' where
    valid: "valid_ownership \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'" "valid_reads m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'" "valid_history program_step ts\<^sub>s\<^sub>b'"
    "valid_sharing \<S>\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b'" "tmps_distinct ts\<^sub>s\<^sub>b'" "valid_data_dependency ts\<^sub>s\<^sub>b'"
    "valid_sops ts\<^sub>s\<^sub>b'" "load_tmps_fresh ts\<^sub>s\<^sub>b'" "enough_flushs ts\<^sub>s\<^sub>b'"
    "valid_program_history ts\<^sub>s\<^sub>b'" "valid ts\<^sub>s\<^sub>b'" and
    last: "(ts'', m'', \<S>'') \<Rightarrow>\<^sub>d\<^sup>* (ts', m', \<S>')" and
    sim': "(ts\<^sub>s\<^sub>b', m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b') \<sim> (ts', m',\<S>')"
    by blast

  note steps also note last
  finally show ?case
    using valid sim'
    by blast
qed

(* FIXME: move up *)
sublocale initial\<^sub>s\<^sub>b \<subseteq> tmps_distinct ..
locale xvalid_program_progress = program_progress + xvalid_program

theorem (in xvalid_program_progress) concurrent_direct_execution_simulates_store_buffer_history_execution:
assumes exec_sb: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b')"
assumes init: "initial\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b"
assumes valid: "valid ts\<^sub>s\<^sub>b" (* FIXME: move into initial ?*)
assumes sim: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<sim> (ts,m,\<S>)"
assumes safe: "safe_reach_direct safe_free_flowing (ts,m,\<S>)"
shows "\<exists>ts' m' \<S>'. (ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>') \<and> 
                (ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b') \<sim> (ts',m',\<S>')"
proof -
  from init interpret ini: initial\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b .
  from safe_free_flowing_implies_safe_delayed' [OF init sim safe]
  have safe_delayed: "safe_reach_direct safe_delayed (ts, m, \<S>)".
  from local.ini.valid_ownership_axioms have "valid_ownership \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b" .
  from local.ini.valid_reads_axioms have "valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b".
  from local.ini.valid_history_axioms have "valid_history program_step ts\<^sub>s\<^sub>b".
  from local.ini.valid_sharing_axioms have "valid_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b".
  from local.ini.tmps_distinct_axioms have "tmps_distinct ts\<^sub>s\<^sub>b".
  from local.ini.valid_sops_axioms have "valid_sops ts\<^sub>s\<^sub>b".
  from local.ini.valid_data_dependency_axioms have "valid_data_dependency ts\<^sub>s\<^sub>b".  
  from local.ini.load_tmps_fresh_axioms have "load_tmps_fresh ts\<^sub>s\<^sub>b".
  from local.ini.enough_flushs_axioms have "enough_flushs ts\<^sub>s\<^sub>b".
  from local.ini.valid_program_history_axioms have "valid_program_history ts\<^sub>s\<^sub>b".
  from concurrent_direct_steps_simulates_store_buffer_history_steps [OF exec_sb 
    \<open>valid_ownership \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close>
    \<open>valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> \<open>valid_history program_step ts\<^sub>s\<^sub>b\<close>
    \<open>valid_sharing \<S>\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<close> \<open>tmps_distinct ts\<^sub>s\<^sub>b\<close> \<open>valid_sops ts\<^sub>s\<^sub>b\<close>
    \<open>valid_data_dependency ts\<^sub>s\<^sub>b\<close> \<open>load_tmps_fresh ts\<^sub>s\<^sub>b\<close> \<open>enough_flushs ts\<^sub>s\<^sub>b\<close>
   \<open>valid_program_history ts\<^sub>s\<^sub>b\<close> valid sim safe_delayed]
  show ?thesis by auto
qed





lemma filter_is_Write\<^sub>s\<^sub>b_Cons_Write\<^sub>s\<^sub>b: "filter is_Write\<^sub>s\<^sub>b xs = Write\<^sub>s\<^sub>b volatile a sop v A L R W#ys
      \<Longrightarrow> \<exists>rs rws. (\<forall>r \<in> set rs. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r) \<and> 
              xs=rs@Write\<^sub>s\<^sub>b volatile a sop v A L R W#rws \<and> ys=filter is_Write\<^sub>s\<^sub>b rws"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  note feq = \<open>filter is_Write\<^sub>s\<^sub>b (x#xs) = Write\<^sub>s\<^sub>b volatile a sop v A L R W# ys\<close>
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile' a' sop' v' A' L' R' W')
    with feq obtain "volatile'=volatile" "a'=a" "v'=v" "sop'=sop" "A'=A" "L'=L" "R'=R" "W'=W"
      "ys = filter is_Write\<^sub>s\<^sub>b xs"
      by auto
    thus ?thesis
      apply -
      apply (rule_tac x="[]" in exI)
      apply (rule_tac x="xs" in exI)
      apply (simp add: Write\<^sub>s\<^sub>b)
      done
  next
    case (Read\<^sub>s\<^sub>b volatile' a' t' v')
    from feq have "filter is_Write\<^sub>s\<^sub>b xs = Write\<^sub>s\<^sub>b volatile a sop v A L R W#ys"
      by (simp add: Read\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] obtain rs rws where
      "\<forall>r \<in> set rs. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r" and
      "xs=rs @ Write\<^sub>s\<^sub>b volatile a sop v A L R W# rws" and
      "ys=filter is_Write\<^sub>s\<^sub>b rws"
      by clarsimp
    then show ?thesis
      apply -
      apply (rule_tac x="Read\<^sub>s\<^sub>b volatile' a' t' v'#rs" in exI)
      apply (rule_tac x="rws" in exI)
      apply (simp add: Read\<^sub>s\<^sub>b)
      done
  next
    case (Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis)
    from feq have "filter is_Write\<^sub>s\<^sub>b xs = Write\<^sub>s\<^sub>b volatile a sop v A L R W#ys"
      by (simp add: Prog\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] obtain rs rws where
      "\<forall>r \<in> set rs. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r" and
      "xs=rs @ Write\<^sub>s\<^sub>b volatile a sop v A L R W# rws" and
      "ys=filter is_Write\<^sub>s\<^sub>b rws"
      by clarsimp
    then show ?thesis
      apply -
      apply (rule_tac x="Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis#rs" in exI)
      apply (rule_tac x="rws" in exI)
      apply (simp add: Prog\<^sub>s\<^sub>b)
      done
    next
    case (Ghost\<^sub>s\<^sub>b A' L' R' W')
    from feq have "filter is_Write\<^sub>s\<^sub>b xs = Write\<^sub>s\<^sub>b volatile a sop v A L R W # ys"
      by (simp add: Ghost\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] obtain rs rws where
      "\<forall>r \<in> set rs. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r" and
      "xs=rs @ Write\<^sub>s\<^sub>b volatile a sop v A L R W# rws" and
      "ys=filter is_Write\<^sub>s\<^sub>b rws"
      by clarsimp
    then show ?thesis
      apply -
      apply (rule_tac x="Ghost\<^sub>s\<^sub>b A' L' R' W'#rs" in exI)
      apply (rule_tac x="rws" in exI)
      apply (simp add: Ghost\<^sub>s\<^sub>b)
      done
  qed
qed

lemma filter_is_Write\<^sub>s\<^sub>b_empty: "filter is_Write\<^sub>s\<^sub>b xs = []
      \<Longrightarrow> (\<forall>r \<in> set xs. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r)"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  note feq = \<open>filter is_Write\<^sub>s\<^sub>b (x#xs) = []\<close>
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile' a' v')
    with feq have False
      by simp
    thus ?thesis ..
  next
    case (Read\<^sub>s\<^sub>b a' v')
    from feq have "filter is_Write\<^sub>s\<^sub>b xs = []"
      by (simp add: Read\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] obtain 
      "\<forall>r \<in> set xs. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r" 
      by clarsimp
    then show ?thesis
      by (simp add: Read\<^sub>s\<^sub>b)
  next
    case (Prog\<^sub>s\<^sub>b p\<^sub>2 p\<^sub>2 mis)
    from feq have "filter is_Write\<^sub>s\<^sub>b xs = []"
      by (simp add: Prog\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] obtain 
      "\<forall>r \<in> set xs. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r" 
      by clarsimp
    then show ?thesis
      by (simp add: Prog\<^sub>s\<^sub>b)
  next
    case (Ghost\<^sub>s\<^sub>b A' L' R' W')
    from feq have "filter is_Write\<^sub>s\<^sub>b xs = []"
      by (simp add: Ghost\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] obtain 
      "\<forall>r \<in> set xs. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r" 
      by clarsimp
    then show ?thesis
      by (simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

lemma flush_reads_program: "\<And>\<O> \<S> \<R> .
  \<forall>r \<in> set sb. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r \<Longrightarrow> 
\<exists>\<O>' \<R>' \<S>'. (m,sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f\<^sup>* (m,[],\<O>',\<R>',\<S>')"      
proof (induct sb)
  case Nil thus ?case by auto
next
  case (Cons x sb)
  note \<open>\<forall>r\<in>set (x # sb). is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r\<close>
  then obtain  x: "is_Read\<^sub>s\<^sub>b x \<or> is_Prog\<^sub>s\<^sub>b x \<or> is_Ghost\<^sub>s\<^sub>b x" and sb: "\<forall>r\<in>set sb. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r"
    by (cases x) auto

  
  {
    assume "is_Read\<^sub>s\<^sub>b x"
    then obtain volatile a t v where x: "x=Read\<^sub>s\<^sub>b volatile a t v"
      by (cases x) auto
    
    have "(m,Read\<^sub>s\<^sub>b volatile a t v#sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m,sb,\<O>,\<R>,\<S>)"
      by (rule Read\<^sub>s\<^sub>b)
    also
    from Cons.hyps [OF sb] obtain \<O>' \<S>' acq' \<R>'
      where "(m, sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f\<^sup>* (m, [],\<O>',\<R>',\<S>')" by blast
    finally
    have ?case
      by (auto simp add: x)
  }
  moreover
  {
    assume "is_Prog\<^sub>s\<^sub>b x"
    then obtain p\<^sub>1 p\<^sub>2 mis  where x: "x=Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis"
      by (cases x) auto
    
    have "(m,Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis#sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m,sb,\<O>,\<R>,\<S>)"
      by (rule Prog\<^sub>s\<^sub>b)
    also
    from Cons.hyps [OF sb] obtain \<O>' \<R>' \<S>' acq' 
    where "(m, sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f\<^sup>* (m, [],\<O>',\<R>',\<S>')" by blast
    finally
    have ?case
      by (auto simp add: x)
  }
  moreover
  {
    assume "is_Ghost\<^sub>s\<^sub>b x"
    then obtain A L R W where x: "x=Ghost\<^sub>s\<^sub>b A L R W"
      by (cases x) auto
    
    have "(m,Ghost\<^sub>s\<^sub>b A L R W#sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m,sb,\<O> \<union> A - R,augment_rels (dom \<S>) R \<R>,\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
      by (rule Ghost)
    also
    from Cons.hyps [OF sb] obtain \<O>' \<S>' \<R>' acq'
    where "(m, sb,\<O> \<union> A - R ,augment_rels (dom \<S>) R \<R>,\<S> \<oplus>\<^bsub>W\<^esub> R  \<ominus>\<^bsub>A\<^esub> L) \<rightarrow>\<^sub>f\<^sup>* (m, [],\<O>',\<R>',\<S>')" by blast
    finally
    have ?case
      by (auto simp add: x)
  }
  ultimately show ?case
    using x by blast
qed


lemma flush_progress: "\<exists>m' \<O>' \<S>' \<R>'. (m,r#sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m',sb,\<O>',\<R>',\<S>')"
proof (cases r)
  case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
  from flush_step.Write\<^sub>s\<^sub>b  [OF refl refl refl, of m volatile a sop v A L R W sb \<O> \<R> \<S>]
  show ?thesis
    by (auto simp add: Write\<^sub>s\<^sub>b)
next
  case (Read\<^sub>s\<^sub>b volatile a t v)
  from flush_step.Read\<^sub>s\<^sub>b [of m volatile a t v sb \<O> \<R> \<S>]
  show ?thesis
    by (auto simp add: Read\<^sub>s\<^sub>b)
next
  case (Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis)
  from flush_step.Prog\<^sub>s\<^sub>b [of m p\<^sub>1 p\<^sub>2 mis sb \<O> \<R> \<S>]  
  show ?thesis
    by (auto simp add: Prog\<^sub>s\<^sub>b)
next
  case (Ghost\<^sub>s\<^sub>b A L R W)
  from flush_step.Ghost [of m A L R W sb \<O> \<R> \<S>]
  show ?thesis
    by (auto simp add: Ghost\<^sub>s\<^sub>b)
qed

lemma flush_empty: 
  assumes steps: "(m, sb,\<O>,\<R>, \<S>) \<rightarrow>\<^sub>f\<^sup>* (m', sb',\<O>',\<R>',\<S>')"
  shows "sb=[] \<Longrightarrow> m'=m \<and> sb'=[] \<and> \<O>'=\<O> \<and> \<R>'=\<R> \<and> \<S>'=\<S> "
using steps
apply (induct rule:  converse_rtranclp_induct5)
apply (auto elim: flush_step.cases)
done

lemma flush_append: 
  assumes steps: "(m, sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f\<^sup>* (m', sb',\<O>',\<R>',\<S>')" 
  shows "\<And>xs. (m, sb@xs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f\<^sup>* (m', sb'@xs,\<O>',\<R>',\<S>')"
using steps
proof (induct rule: converse_rtranclp_induct5)
  case refl thus ?case by auto
next
  case (step m sb \<O> \<R> \<S> m'' sb'' \<O>'' \<R>'' \<S>'')
  note first=  \<open>(m,sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m'',sb'',\<O>'',\<R>'',\<S>'')\<close>
  note rest = \<open>(m'', sb'',\<O>'',\<R>'',\<S>'') \<rightarrow>\<^sub>f\<^sup>* (m', sb',\<O>',\<R>',\<S>')\<close>
  from step.hyps (3)  have append_rest: "(m'', sb''@xs,\<O>'',\<R>'',\<S>'') \<rightarrow>\<^sub>f\<^sup>* (m', sb'@xs,\<O>',\<R>',\<S>')".
  from first show ?case
  proof (cases)
    case (Write\<^sub>s\<^sub>b volatile A R W L a sop v)
    then obtain sb: "sb=Write\<^sub>s\<^sub>b volatile a sop v A L R W#sb''" and m'': "m''=m(a:=v)" and 
      \<O>'': "\<O>''=(if volatile then \<O> \<union> A - R else \<O>)" and
      \<R>'': "\<R>''=(if volatile then Map.empty else \<R>)" and
      \<S>'': "\<S>''=(if volatile then \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L else \<S>)"
      by auto
    have "(m,Write\<^sub>s\<^sub>b volatile a sop v A L R W#sb''@xs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f 
      (m(a:=v),sb''@xs,if volatile then \<O> \<union> A - R else \<O>,if volatile then Map.empty else \<R>,
      if volatile then \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L else \<S>)"
      apply (rule flush_step.Write\<^sub>s\<^sub>b)
      apply auto
      done
    hence "(m,sb@xs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m'',sb''@xs,\<O>'',\<R>'',\<S>'')"
      by (simp add: sb m'' \<O>'' \<R>'' \<S>'')
    also note append_rest
    finally show ?thesis .
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    then obtain sb: "sb=Read\<^sub>s\<^sub>b volatile a t v #sb''" and m'': "m''=m" 
      and \<O>'': "\<O>''=\<O>" and \<S>'': "\<S>''=\<S>" and \<R>'': "\<R>''=\<R>" 
      by auto
    have "(m,Read\<^sub>s\<^sub>b volatile a t v#sb''@xs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m,sb''@xs,\<O>,\<R>,\<S>)"
      by (rule flush_step.Read\<^sub>s\<^sub>b)
    hence "(m,sb@xs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m'',sb''@xs,\<O>'',\<R>'',\<S>'')"
      by (simp add: sb m'' \<O>'' \<R>'' \<S>'' )
    also note append_rest
    finally show ?thesis .
  next
    case (Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis)
    then obtain sb: "sb=Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis#sb''" and m'': "m''=m"
      and \<O>'': "\<O>''=\<O>" and \<S>'': "\<S>''=\<S>" and \<R>'': "\<R>''=\<R>" 
      by auto
    have "(m,Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis#sb''@xs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m,sb''@xs,\<O>,\<R>,\<S>)"
      by (rule flush_step.Prog\<^sub>s\<^sub>b)
    hence "(m,sb@xs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m'',sb''@xs,\<O>'',\<R>'',\<S>'')"
      by (simp add: sb m'' \<O>'' \<R>'' \<S>'' ) 
    also note append_rest
    finally show ?thesis .
  next
    case (Ghost A L R W)
    then obtain sb: "sb=Ghost\<^sub>s\<^sub>b A L R W#sb''" and m'': "m''=m"
      and \<O>'': "\<O>''=\<O> \<union> A - R" and \<S>'': "\<S>''=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub>  L" and 
      \<R>'': "\<R>''=augment_rels (dom \<S>) R \<R>"
      by auto
    have "(m,Ghost\<^sub>s\<^sub>b A L R W#sb''@xs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m,sb''@xs,\<O> \<union> A - R,augment_rels (dom \<S>) R \<R>,\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
      by (rule flush_step.Ghost)
    hence "(m,sb@xs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m'',sb''@xs,\<O>'',\<R>'',\<S>'')"
      by (simp add: sb m'' \<O>'' \<R>'' \<S>'' )
    also note append_rest
    finally show ?thesis .
  qed
qed
(*
theorem flush_simulates_filter_writes:
  assumes step: "(m,sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m',sb',\<O>',\<R>',\<S>')"
  shows "\<And>sb\<^sub>h \<O>\<^sub>h \<R>\<^sub>h \<S>\<^sub>h. sb=filter is_Write\<^sub>s\<^sub>b sb\<^sub>h 
          \<Longrightarrow> 
          \<exists>sb\<^sub>h' \<O>\<^sub>h' \<R>\<^sub>h' \<S>\<^sub>h'. (m,sb\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>f\<^sup>* (m',sb\<^sub>h',\<O>\<^sub>h',\<R>\<^sub>h',\<S>\<^sub>h') \<and> 
  sb'=filter is_Write\<^sub>s\<^sub>b sb\<^sub>h'"
using step
proof (induct rule: flush_step_induct)
  case (Write\<^sub>s\<^sub>b \<O>' volatile \<O> A R \<S>' \<S> W L \<R>' \<R>  m a D f v sb)
  note filter_Write\<^sub>s\<^sub>b = `Write\<^sub>s\<^sub>b volatile a (D,f) v A L R W# sb = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h`
  note \<O>' = `\<O>' = (if volatile then \<O> \<union> A - R else \<O>)`
  note \<R>' = `\<R>'= (if volatile then empty else \<R>)`
  note \<S>' = `\<S>' = (if volatile then \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L else \<S>)`
  from filter_is_Write\<^sub>s\<^sub>b_Cons_Write\<^sub>s\<^sub>b [OF filter_Write\<^sub>s\<^sub>b [symmetric]]
  obtain rs rws where
    rs_reads: "\<forall>r\<in>set rs. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r" and
    sb\<^sub>h: "sb\<^sub>h = rs @ Write\<^sub>s\<^sub>b volatile a (D,f) v A L R W# rws" and 
    sb: "sb = filter is_Write\<^sub>s\<^sub>b rws"
    by blast

  from flush_reads_program [OF rs_reads] obtain \<O>\<^sub>h' \<R>\<^sub>h' \<S>\<^sub>h' acq\<^sub>h'
  where "(m, rs,\<O>\<^sub>h,\<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>f\<^sup>* (m, [],\<O>\<^sub>h',\<R>\<^sub>h',\<S>\<^sub>h')" by blast
  from flush_append [OF this]
  have "(m, rs@Write\<^sub>s\<^sub>b volatile a (D,f) v A L R W# rws,\<O>\<^sub>h,\<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>f\<^sup>* 
       (m, Write\<^sub>s\<^sub>b volatile a (D,f) v A L R W# rws,\<O>\<^sub>h',\<R>\<^sub>h',\<S>\<^sub>h')"
    by simp
  also
  from flush_step.Write\<^sub>s\<^sub>b [OF refl refl refl, of m volatile a "(D,f)" v A L R W rws \<O>\<^sub>h' \<R>\<^sub>h' \<S>\<^sub>h']
  obtain \<O>\<^sub>h'' \<R>\<^sub>h'' \<S>\<^sub>h'' 
  where  "(m, Write\<^sub>s\<^sub>b volatile a (D,f) v A L R W# rws,\<O>\<^sub>h',\<R>\<^sub>h',\<S>\<^sub>h') \<rightarrow>\<^sub>f (m(a:=v), rws, \<O>\<^sub>h'',\<R>\<^sub>h'',\<S>\<^sub>h'')"
    by auto
  finally have "(m, sb\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>f\<^sup>* (m(a:=v), rws,\<O>\<^sub>h'',\<R>\<^sub>h'',\<S>\<^sub>h'')"
    by (simp add: sb\<^sub>h sb)
  with sb show ?case
    by blast
next
  case (Read\<^sub>s\<^sub>b m volatile a t v sb) 
  note `Read\<^sub>s\<^sub>b volatile a t v # sb = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h`
  from this [symmetric]
  have r_in: "Read\<^sub>s\<^sub>b volatile a t v \<in> set (filter is_Write\<^sub>s\<^sub>b sb\<^sub>h)"
    by auto
  have "\<forall>r \<in> set (filter is_Write\<^sub>s\<^sub>b sb\<^sub>h). is_Write\<^sub>s\<^sub>b r"
    by auto
  from this [rule_format, OF r_in]
  have False by simp
  thus ?case ..
next
  case (Prog\<^sub>s\<^sub>b m p\<^sub>1 p\<^sub>2 mis sb)
  note `Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis # sb = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h`
  from this [symmetric]
  have r_in: "Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis \<in> set (filter is_Write\<^sub>s\<^sub>b sb\<^sub>h)"
    by auto
  have "\<forall>r \<in> set (filter is_Write\<^sub>s\<^sub>b sb\<^sub>h). is_Write\<^sub>s\<^sub>b r"
    by auto
  from this [rule_format, OF r_in]
  have False by simp
  thus ?case ..
next
  case (Ghost m A L R W sb)
  note `Ghost\<^sub>s\<^sub>b A L R W# sb = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h`
  from this [symmetric]
  have r_in: "Ghost\<^sub>s\<^sub>b A L R W\<in> set (filter is_Write\<^sub>s\<^sub>b sb\<^sub>h)"
    by auto
  have "\<forall>r \<in> set (filter is_Write\<^sub>s\<^sub>b sb\<^sub>h). is_Write\<^sub>s\<^sub>b r"
    by auto
  from this [rule_format, OF r_in]
  have False by simp
  thus ?case ..
qed
*)
(* FIXME: move up *)
lemmas store_buffer_step_induct =  
  store_buffer_step.induct [split_format (complete),
  consumes 1, case_names SBWrite\<^sub>s\<^sub>b]
theorem flush_simulates_filter_writes:
  assumes step: "(m,sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>w (m',sb',\<O>',\<R>',\<S>')"
  shows "\<And>sb\<^sub>h \<O>\<^sub>h \<R>\<^sub>h \<S>\<^sub>h. sb=filter is_Write\<^sub>s\<^sub>b sb\<^sub>h 
          \<Longrightarrow> 
          \<exists>sb\<^sub>h' \<O>\<^sub>h' \<R>\<^sub>h' \<S>\<^sub>h'. (m,sb\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>f\<^sup>* (m',sb\<^sub>h',\<O>\<^sub>h',\<R>\<^sub>h',\<S>\<^sub>h') \<and> 
  sb'=filter is_Write\<^sub>s\<^sub>b sb\<^sub>h' \<and> (sb'=[] \<longrightarrow> sb\<^sub>h'=[])"
using step
proof (induct rule: store_buffer_step_induct)
  case (SBWrite\<^sub>s\<^sub>b m volatile a D f v A L R W sb \<O> \<R> \<S>)
  note filter_Write\<^sub>s\<^sub>b = \<open>Write\<^sub>s\<^sub>b volatile a (D,f) v A L R W# sb = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h\<close>
  
  from filter_is_Write\<^sub>s\<^sub>b_Cons_Write\<^sub>s\<^sub>b [OF filter_Write\<^sub>s\<^sub>b [symmetric]]
  obtain rs rws where
    rs_reads: "\<forall>r\<in>set rs. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r" and
    sb\<^sub>h: "sb\<^sub>h = rs @ Write\<^sub>s\<^sub>b volatile a (D,f) v A L R W# rws" and 
    sb: "sb = filter is_Write\<^sub>s\<^sub>b rws"
    by blast

  from flush_reads_program [OF rs_reads] obtain \<O>\<^sub>h' \<R>\<^sub>h' \<S>\<^sub>h' acq\<^sub>h'
  where "(m, rs,\<O>\<^sub>h,\<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>f\<^sup>* (m, [],\<O>\<^sub>h',\<R>\<^sub>h',\<S>\<^sub>h')" by blast
  from flush_append [OF this]
  have "(m, rs@Write\<^sub>s\<^sub>b volatile a (D,f) v A L R W# rws,\<O>\<^sub>h,\<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>f\<^sup>* 
       (m, Write\<^sub>s\<^sub>b volatile a (D,f) v A L R W# rws,\<O>\<^sub>h',\<R>\<^sub>h',\<S>\<^sub>h')"
    by simp
  also
  from flush_step.Write\<^sub>s\<^sub>b [OF refl refl refl, of m volatile a "(D,f)" v A L R W rws \<O>\<^sub>h' \<R>\<^sub>h' \<S>\<^sub>h']
  obtain \<O>\<^sub>h'' \<R>\<^sub>h'' \<S>\<^sub>h'' 
  where  "(m, Write\<^sub>s\<^sub>b volatile a (D,f) v A L R W# rws,\<O>\<^sub>h',\<R>\<^sub>h',\<S>\<^sub>h') \<rightarrow>\<^sub>f (m(a:=v), rws, \<O>\<^sub>h'',\<R>\<^sub>h'',\<S>\<^sub>h'')"
    by auto
  finally have steps: "(m, sb\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>f\<^sup>* (m(a:=v), rws,\<O>\<^sub>h'',\<R>\<^sub>h'',\<S>\<^sub>h'')"
    by (simp add: sb\<^sub>h sb)
  show ?case
  proof (cases "sb")
    case Cons
    with steps sb show ?thesis 
      by fastforce
  next  
    case Nil
    from filter_is_Write\<^sub>s\<^sub>b_empty [OF sb [simplified Nil, symmetric]]
    have "\<forall>r\<in>set rws. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r".
    from flush_reads_program [OF this] obtain \<O>\<^sub>h''' \<R>\<^sub>h''' \<S>\<^sub>h''' acq\<^sub>h'''
      where "(m(a:=v), rws,\<O>\<^sub>h'',\<R>\<^sub>h'',\<S>\<^sub>h'') \<rightarrow>\<^sub>f\<^sup>* (m(a:=v), [],\<O>\<^sub>h''',\<R>\<^sub>h''',\<S>\<^sub>h''')" by blast
    with steps 
    have "(m, sb\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>f\<^sup>* (m(a:=v), [],\<O>\<^sub>h''',\<R>\<^sub>h''',\<S>\<^sub>h''')" by force
    with sb Nil show ?thesis by fastforce
  qed
qed

lemma bufferd_val_filter_is_Write\<^sub>s\<^sub>b_eq_ext:
  "buffered_val (filter is_Write\<^sub>s\<^sub>b sb) a = buffered_val sb a" 
  by (induct sb) (auto split: memref.splits)

lemma bufferd_val_filter_is_Write\<^sub>s\<^sub>b_eq:
  "buffered_val (filter is_Write\<^sub>s\<^sub>b sb) = buffered_val sb"
  by (rule ext) (rule bufferd_val_filter_is_Write\<^sub>s\<^sub>b_eq_ext)

lemma outstanding_refs_is_volatile_Write\<^sub>s\<^sub>b_filter_writes: 
  "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (filter is_Write\<^sub>s\<^sub>b xs) = 
   outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs"
  by (induct xs) (auto simp add: is_volatile_Write\<^sub>s\<^sub>b_def split: memref.splits)

subsection \<open>Simulation of Store Buffer Machine without History by Store Buffer Machine with History\<close>

theorem (in valid_program) concurrent_history_steps_simulates_store_buffer_step:
  assumes step_sb: "(ts,m,\<S>) \<Rightarrow>\<^sub>s\<^sub>b (ts',m',\<S>')"
  assumes sim: "ts \<sim>\<^sub>h ts\<^sub>h"
  shows "\<exists>ts\<^sub>h' \<S>\<^sub>h'. (ts\<^sub>h,m,\<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>h',m',\<S>\<^sub>h') \<and> ts' \<sim>\<^sub>h ts\<^sub>h'"
proof -
  interpret sbh_computation: 
    computation sbh_memop_step flush_step program_step 
       "\<lambda>p p' is sb. sb @ [Prog\<^sub>s\<^sub>b p p' is]" .
  from step_sb
  show ?thesis
  proof (cases rule: concurrent_step_cases)
    case (Memop i _ p "is" \<theta> sb \<D> \<O> \<R>  _ _ is' \<theta>' sb' _ \<D>' \<O>' \<R>')
    then obtain
      ts': "ts' = ts[i := (p, is', \<theta>', sb', \<D>', \<O>',\<R>')]" and
      i_bound: "i < length ts" and
      ts_i: "ts ! i = (p, is, \<theta>, sb, \<D>, \<O>,\<R>)" and
      step_sb: "(is, \<theta>, sb, m, \<D>, \<O>, \<R>,\<S>) \<rightarrow>\<^sub>s\<^sub>b 
                                (is', \<theta>', sb', m', \<D>', \<O>', \<R>',\<S>')"
      by auto
  
    from sim obtain 
      lts_eq: "length ts = length ts\<^sub>h" and
      sim_loc: "\<forall>i < length ts. (\<exists>\<O>' \<D>' \<R>'.
            let (p,is, \<theta>, sb,\<D>, \<O>,\<R>) = ts\<^sub>h!i in 
             ts!i=(p,is, \<theta>, filter is_Write\<^sub>s\<^sub>b sb,\<D>',\<O>',\<R>') \<and>
             (filter is_Write\<^sub>s\<^sub>b sb = [] \<longrightarrow> sb=[]))"
      by cases (auto)

    from lts_eq i_bound have i_bound': "i < length ts\<^sub>h"
      by simp

    from step_sb
    show ?thesis
    proof (cases)
      case (SBReadBuffered a v volatile t)
      then obtain
	"is": "is = Read volatile a t#is'" and
	\<O>': "\<O>'=\<O>" and
	\<S>': "\<S>'=\<S>" and
        \<R>': "\<R>'=\<R>" and
	\<D>': "\<D>'=\<D>" and
	m': "m'=m" and
	\<theta>': "\<theta>'=\<theta>(t\<mapsto>v)" and
	sb': "sb' = sb" and
	buf_val: "buffered_val sb a = Some v"
	by auto
      
      from sim_loc [rule_format, OF i_bound] ts_i "is" 
      obtain sb\<^sub>h \<O>\<^sub>h \<R>\<^sub>h \<D>\<^sub>h where 
	ts\<^sub>h_i: "ts\<^sub>h!i = (p,Read volatile a t#is',\<theta>,sb\<^sub>h,\<D>\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h)" and
	sb: "sb = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h" and
        sb_empty: "filter is_Write\<^sub>s\<^sub>b sb\<^sub>h = [] \<longrightarrow> sb\<^sub>h=[]"
	by (auto simp add: Let_def)

      from buf_val
      have buf_val': "buffered_val sb\<^sub>h a = Some v"
	by (simp add: bufferd_val_filter_is_Write\<^sub>s\<^sub>b_eq sb)

      let ?ts\<^sub>h_i' = "(p, is', \<theta>(t \<mapsto> v), sb\<^sub>h @ [Read\<^sub>s\<^sub>b volatile a t v], \<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)"
      let ?ts\<^sub>h' = "ts\<^sub>h[i := ?ts\<^sub>h_i']" 
      from sbh_memop_step.SBHReadBuffered [OF buf_val'] 
      have "(Read volatile a t # is', \<theta>, sb\<^sub>h, m,\<D>\<^sub>h, \<O>\<^sub>h, \<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h 
            (is', \<theta>(t \<mapsto> v), sb\<^sub>h@ [Read\<^sub>s\<^sub>b volatile a t v], m, \<D>\<^sub>h, \<O>\<^sub>h, \<R>\<^sub>h, \<S>\<^sub>h)".
      from sbh_computation.Memop [OF i_bound' ts\<^sub>h_i this] 
      have step: "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h (?ts\<^sub>h', m, \<S>\<^sub>h)".

      from sb have sb: "sb = filter is_Write\<^sub>s\<^sub>b (sb\<^sub>h @ [Read\<^sub>s\<^sub>b volatile a t v])"
	by simp

      show ?thesis
      proof (cases "filter is_Write\<^sub>s\<^sub>b sb\<^sub>h = []")
        case False

        have "ts [i := (p,is',\<theta>(t \<mapsto> v),sb,\<D>,\<O>,\<R>)] \<sim>\<^sub>h ?ts\<^sub>h'"
          apply (rule sim_history_config.intros)
	  using lts_eq
	  apply  simp
	  using sim_loc i_bound i_bound' sb sb_empty False
	  apply (auto simp add: Let_def nth_list_update)
	  done

        with step show ?thesis
	  by (auto simp del: fun_upd_apply simp add: \<S>' m' ts' \<O>' \<theta>' \<D>' sb' \<R>')
      next
        case True
        with sb_empty have empty: "sb\<^sub>h=[]" by simp
        from i_bound' have "?ts\<^sub>h'!i = ?ts\<^sub>h_i'"
          by auto

        
        from sbh_computation.StoreBuffer [OF _ this, simplified empty, simplified, OF _ flush_step.Read\<^sub>s\<^sub>b, of m \<S>\<^sub>h] i_bound'
        have "(?ts\<^sub>h', m, \<S>\<^sub>h)
              \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h  (ts\<^sub>h[i := (p, is', \<theta>(t \<mapsto> v), [], \<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)], m, \<S>\<^sub>h)"
          by (simp add: empty list_update_overwrite)
        with step have "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>*
              (ts\<^sub>h[i := (p, is', \<theta>(t \<mapsto> v), [], \<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)], m,\<S>\<^sub>h)"
          by force
        moreover
        have "ts [i := (p,is',\<theta>(t \<mapsto> v),sb,\<D>,\<O>,\<R>)] \<sim>\<^sub>h ts\<^sub>h[i := (p, is', \<theta>(t \<mapsto> v), [], \<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)]"
          apply (rule sim_history_config.intros)
	  using lts_eq
	  apply  simp
	  using sim_loc i_bound i_bound' sb empty 
	  apply (auto simp add: Let_def nth_list_update)
	  done
        ultimately show ?thesis
	  by (auto simp del: fun_upd_apply simp add: \<S>' m' ts' \<O>' \<theta>' \<D>' sb' \<R>')
      qed
    next
      case (SBReadUnbuffered a volatile t)
      then obtain
	"is": "is = Read volatile a t#is'" and
	\<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
	\<S>': "\<S>'=\<S>" and
	\<D>': "\<D>'=\<D>" and
	m': "m'=m" and
	\<theta>': "\<theta>'=\<theta>(t\<mapsto>m a)" and
	sb': "sb' = sb" and
	buf: "buffered_val sb a = None"
	by auto
    
      from sim_loc [rule_format, OF i_bound] ts_i "is"
      obtain sb\<^sub>h \<O>\<^sub>h \<R>\<^sub>h \<D>\<^sub>h where 
	ts\<^sub>h_i: "ts\<^sub>h!i = (p,Read volatile a t#is',\<theta>,sb\<^sub>h,\<D>\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h)" and
	sb: "sb = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h" and
        sb_empty: "filter is_Write\<^sub>s\<^sub>b sb\<^sub>h = [] \<longrightarrow> sb\<^sub>h=[]"
	by (auto simp add: Let_def)

      from buf
      have buf': "buffered_val sb\<^sub>h a = None"
	by (simp add: bufferd_val_filter_is_Write\<^sub>s\<^sub>b_eq sb)

      let ?ts\<^sub>h_i' = "(p, is', \<theta>(t \<mapsto> m a), sb\<^sub>h @ [Read\<^sub>s\<^sub>b volatile a t (m a)], \<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)"
      let ?ts\<^sub>h' = "ts\<^sub>h[i := ?ts\<^sub>h_i']" 

      from sbh_memop_step.SBHReadUnbuffered [OF buf']
      have "(Read volatile a t # is',\<theta>, sb\<^sub>h, m, \<D>\<^sub>h, \<O>\<^sub>h, \<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h 
            (is', \<theta>(t \<mapsto> (m a)), sb\<^sub>h@ [Read\<^sub>s\<^sub>b volatile a t (m a)], m,\<D>\<^sub>h, \<O>\<^sub>h, \<R>\<^sub>h,\<S>\<^sub>h)".
      from sbh_computation.Memop [OF i_bound' ts\<^sub>h_i this] 
      have step: "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h 
            (?ts\<^sub>h', m, \<S>\<^sub>h)".
      moreover 
      from sb have sb: "sb = filter is_Write\<^sub>s\<^sub>b (sb\<^sub>h @ [Read\<^sub>s\<^sub>b volatile a t (m a)])"
	by simp
    
      show ?thesis
      proof (cases "filter is_Write\<^sub>s\<^sub>b sb\<^sub>h = []")
        case False
        have "ts [i := (p,is',\<theta> (t\<mapsto>m a),sb,\<D>,\<O>,\<R>)] \<sim>\<^sub>h ?ts\<^sub>h'"
	  apply (rule sim_history_config.intros)
	  using lts_eq
	  apply  simp
	  using sim_loc i_bound i_bound' sb sb_empty False
	  apply (auto simp add: Let_def nth_list_update)
	  done
 
        with step show ?thesis
	  by (auto simp del: fun_upd_apply simp add: \<S>' m' ts' \<O>' \<R>' \<D>' \<theta>' sb')
      next
        case True
        with sb_empty have empty: "sb\<^sub>h=[]" by simp
        from i_bound' have "?ts\<^sub>h'!i = ?ts\<^sub>h_i'"
          by auto

        
        from sbh_computation.StoreBuffer [OF _ this, simplified empty, simplified, OF _ flush_step.Read\<^sub>s\<^sub>b, of m \<S>\<^sub>h] i_bound'
        have "(?ts\<^sub>h', m, \<S>\<^sub>h)
              \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h  (ts\<^sub>h[i := (p, is', \<theta>(t \<mapsto> (m a)), [], \<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)], m, \<S>\<^sub>h)"
          by (simp add: empty)
        with step have "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>*
              (ts\<^sub>h[i := (p, is', \<theta>(t \<mapsto> m a), [], \<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)], m, \<S>\<^sub>h)"
          by force
        moreover
        have "ts [i := (p,is',\<theta>(t \<mapsto> m a),sb,\<D>,\<O>,\<R>)] \<sim>\<^sub>h ts\<^sub>h[i := (p, is', \<theta>(t \<mapsto> m a), [], \<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)]"
          apply (rule sim_history_config.intros)
	  using lts_eq
	  apply  simp
	  using sim_loc i_bound i_bound' sb empty 
	  apply (auto simp add: Let_def nth_list_update)
	  done
        ultimately show ?thesis
	  by (auto simp del: fun_upd_apply simp add: \<S>' m' ts' \<O>' \<theta>' \<D>' sb' \<R>')
      qed
    next
      case (SBWriteNonVolatile a D f A L R W)
      then obtain
	"is": "is = Write False a (D, f) A L R W#is'" and
	\<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
	\<S>': "\<S>'=\<S>" and
	\<D>': "\<D>'=\<D>" and
	m': "m'=m" and
	\<theta>': "\<theta>'=\<theta>" and
	sb': "sb' = sb@[Write\<^sub>s\<^sub>b False a (D, f) (f \<theta>) A L R W]" 
	by auto

      from sim_loc [rule_format, OF i_bound] ts_i
      obtain sb\<^sub>h \<O>\<^sub>h \<R>\<^sub>h \<D>\<^sub>h where 
	ts\<^sub>h_i: "ts\<^sub>h!i = (p,Write False a (D,f) A L R W#is',\<theta>,sb\<^sub>h,\<D>\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h)" and
	sb: "sb = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h" 
	by (auto simp add: Let_def "is") 

      from sbh_memop_step.SBHWriteNonVolatile 
      have "(Write False a (D, f) A L R W# is',\<theta>, sb\<^sub>h, m, \<D>\<^sub>h, \<O>\<^sub>h, \<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h 
               (is', \<theta>, sb\<^sub>h @ [Write\<^sub>s\<^sub>b False a (D, f) (f \<theta>) A L R W], m,\<D>\<^sub>h, \<O>\<^sub>h, \<R>\<^sub>h,\<S>\<^sub>h)".
      from sbh_computation.Memop [OF i_bound' ts\<^sub>h_i this] 
      have "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h 
            (ts\<^sub>h[i := (p, is',\<theta>, sb\<^sub>h @ [Write\<^sub>s\<^sub>b False a (D, f) (f \<theta>) A L R W], \<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)],
             m, \<S>\<^sub>h)".
      moreover
      have "ts [i := (p,is',\<theta>,sb @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>) A L R W],\<D>,\<O>,\<R>)] \<sim>\<^sub>h 
            ts\<^sub>h[i := (p,is',\<theta>, sb\<^sub>h @ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>) A L R W],\<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)]"
	apply (rule sim_history_config.intros)
	using lts_eq
	apply  simp
	using sim_loc i_bound i_bound' sb 
	apply (auto simp add: Let_def nth_list_update)
	done

      ultimately show ?thesis
	by (auto simp add: \<S>' m' \<theta>' \<O>' \<R>' \<D>' ts' sb')
    next
      case (SBWriteVolatile a D f A L R W)
      then obtain
	"is": "is = Write True a (D, f) A L R W#is'" and
	\<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
	\<S>': "\<S>'=\<S>" and
	\<D>': "\<D>'=\<D>" and
	m': "m'=m" and
	\<theta>': "\<theta>'=\<theta>" and
	sb': "sb' = sb@[Write\<^sub>s\<^sub>b True a (D, f) (f \<theta>) A L R W]" 
	by auto

      from sim_loc [rule_format, OF i_bound] ts_i "is"
      obtain sb\<^sub>h \<O>\<^sub>h \<R>\<^sub>h \<D>\<^sub>h where 
	ts\<^sub>h_i: "ts\<^sub>h!i = (p,Write True a (D,f) A L R W#is',\<theta>,sb\<^sub>h,\<D>\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h)" and
	sb: "sb = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h"
	by (auto simp add: Let_def)

      from sbh_computation.Memop [OF i_bound' ts\<^sub>h_i SBHWriteVolatile 
	]
      have "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h 
            (ts\<^sub>h[i := (p, is',\<theta>, sb\<^sub>h @ [Write\<^sub>s\<^sub>b True a (D, f) (f \<theta>) A L R W], True, \<O>\<^sub>h,\<R>\<^sub>h)],
                m, \<S>\<^sub>h)".

      moreover
      have "ts [i := (p,is',\<theta>,sb @ [Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>) A L R W],\<D>,\<O>,\<R>)] \<sim>\<^sub>h 
            ts\<^sub>h[i := (p,is', \<theta>, sb\<^sub>h @ [Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>) A L R W],True, \<O>\<^sub>h,\<R>\<^sub>h)]"
	apply (rule sim_history_config.intros)
	using lts_eq
	apply  simp
	using sim_loc i_bound i_bound' sb 
	apply (auto simp add: Let_def nth_list_update)
	done

      ultimately show ?thesis
	by (auto simp add: ts' \<O>' \<theta>' m' sb' \<D>' \<R>' \<S>')
    next
      case SBFence
      then obtain
	"is": "is = Fence #is'" and
	\<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
	\<S>': "\<S>'=\<S>" and
	\<D>': "\<D>'=\<D>" and
	m': "m'=m" and
	\<theta>': "\<theta>'=\<theta>" and
	sb: "sb = []" and
	sb': "sb' = []" 
	by auto
      
      from sim_loc [rule_format, OF i_bound] ts_i sb "is"
      obtain sb\<^sub>h \<O>\<^sub>h \<R>\<^sub>h \<D>\<^sub>h where 
	ts\<^sub>h_i: "ts\<^sub>h!i = (p,Fence # is',\<theta>,sb\<^sub>h,\<D>\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h)" and
	sb: "[] = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h"
	by (auto simp add: Let_def)


      from filter_is_Write\<^sub>s\<^sub>b_empty [OF sb [symmetric]]
      have "\<forall>r \<in> set sb\<^sub>h. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r".

      from flush_reads_program [OF this] obtain \<O>\<^sub>h' \<S>\<^sub>h'  \<R>\<^sub>h'
      where flsh: "(m, sb\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>f\<^sup>* (m, [],\<O>\<^sub>h',\<R>\<^sub>h',\<S>\<^sub>h')" by blast

      let ?ts\<^sub>h' = "ts\<^sub>h[i := (p,Fence # is', \<theta>, [], \<D>\<^sub>h, \<O>\<^sub>h',\<R>\<^sub>h')]"
      from sbh_computation.store_buffer_steps [OF flsh i_bound' ts\<^sub>h_i]
      have "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (?ts\<^sub>h', m, \<S>\<^sub>h')".

      also

      from i_bound' have i_bound'': "i < length ?ts\<^sub>h'"
	by auto

      from i_bound' have ts\<^sub>h'_i: "?ts\<^sub>h'!i = (p,Fence#is',\<theta>,[],\<D>\<^sub>h,\<O>\<^sub>h',\<R>\<^sub>h')"
	by simp
      from sbh_computation.Memop [OF i_bound'' ts\<^sub>h'_i SBHFence] i_bound'
      have "(?ts\<^sub>h', m, \<S>\<^sub>h') \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h (ts\<^sub>h[i := (p, is',\<theta>, [], False, \<O>\<^sub>h',Map.empty)], m,\<S>\<^sub>h')"
	by (simp)
      finally
      have "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>h[i := (p, is', \<theta>, [],False, \<O>\<^sub>h',Map.empty)],m, \<S>\<^sub>h')".

      moreover
    
      have "ts [i := (p,is',\<theta>,[],\<D>,\<O>,\<R>)] \<sim>\<^sub>h ts\<^sub>h[i := (p,is', \<theta>, [],False, \<O>\<^sub>h',Map.empty)]"
	apply (rule sim_history_config.intros)
	using lts_eq
	apply  simp
	using sim_loc i_bound i_bound' sb 
	apply (auto simp add: Let_def nth_list_update)
	done

      ultimately show ?thesis
	by (auto simp add: ts' \<O>' \<theta>' m' sb' \<D>' \<S>' \<R>')

    next
      case (SBRMWReadOnly cond t a D f ret A L R W)
      then obtain
	"is": "is = RMW a t (D, f) cond ret A L R W#is'" and
	\<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
	\<S>': "\<S>'=\<S>" and
	\<D>': "\<D>'=\<D>" and
	m': "m'=m" and
	\<theta>': "\<theta>'=\<theta>(t \<mapsto> m a)" and
	sb: "sb=[]" and
	sb': "sb' = []" and
	cond: "\<not> cond (\<theta>(t \<mapsto> m a))"
	by auto      

      from sim_loc [rule_format, OF i_bound] ts_i sb "is"
      obtain sb\<^sub>h \<O>\<^sub>h \<R>\<^sub>h \<D>\<^sub>h where 
	ts\<^sub>h_i: "ts\<^sub>h!i = (p,RMW a t (D, f) cond ret A L R W# is',\<theta>,sb\<^sub>h,\<D>\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h)" and
	sb: "[] = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h"
	by (auto simp add: Let_def)



      from filter_is_Write\<^sub>s\<^sub>b_empty [OF sb [symmetric]]
      have "\<forall>r \<in> set sb\<^sub>h. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r".

      from flush_reads_program [OF this] obtain \<O>\<^sub>h' \<S>\<^sub>h' \<R>\<^sub>h'
      where flsh: "(m, sb\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>f\<^sup>* (m, [],\<O>\<^sub>h',\<R>\<^sub>h',\<S>\<^sub>h')" by blast

      let ?ts\<^sub>h' = "ts\<^sub>h[i := (p,RMW a t (D, f) cond ret A L R W# is',\<theta>, [], \<D>\<^sub>h, \<O>\<^sub>h',\<R>\<^sub>h')]"
      from sbh_computation.store_buffer_steps [OF flsh i_bound' ts\<^sub>h_i]
      have "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (?ts\<^sub>h', m, \<S>\<^sub>h')".

      also

      from i_bound' have i_bound'': "i < length ?ts\<^sub>h'"
	by auto

      from i_bound' have ts\<^sub>h'_i: "?ts\<^sub>h'!i = (p,RMW a t (D, f) cond ret A L R W#is',\<theta>,[],\<D>\<^sub>h,\<O>\<^sub>h',\<R>\<^sub>h')"
	by simp

      note step= SBHRMWReadOnly [where cond=cond and \<theta>=\<theta> and m=m, OF cond ] 
      from sbh_computation.Memop [OF i_bound'' ts\<^sub>h'_i step ] i_bound' 
      have "(?ts\<^sub>h', m, \<S>\<^sub>h') \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h (ts\<^sub>h[i := (p, is',\<theta>(t\<mapsto>m a), [], False, \<O>\<^sub>h',Map.empty)],m, \<S>\<^sub>h')"
	by (simp)
      finally
      have "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>h[i := (p, is',\<theta>(t\<mapsto>m a), [], False, \<O>\<^sub>h',Map.empty)],m, \<S>\<^sub>h')".

      moreover
    
      have "ts [i := (p,is',\<theta>(t\<mapsto>m a),[],\<D>,\<O>,\<R>)] \<sim>\<^sub>h ts\<^sub>h[i := (p,is', \<theta>(t\<mapsto>m a), [], False, \<O>\<^sub>h',Map.empty)]"
	apply (rule sim_history_config.intros)
	using lts_eq
	apply  simp
	using sim_loc i_bound i_bound' sb 
	apply (auto simp add: Let_def nth_list_update)
	done

      ultimately show ?thesis
	by (auto simp add: ts' \<O>' \<theta>' m' sb' \<D>' \<S>' \<R>')
    next
      case (SBRMWWrite cond t a D f ret A L R W)
      then obtain
	"is": "is = RMW a t (D, f) cond ret A L R W#is'" and
	\<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
	\<S>': "\<S>'=\<S>" and
	\<D>': "\<D>'=\<D>" and
	m': "m'=m(a := f (\<theta>(t \<mapsto> (m a))))" and
	\<theta>': "\<theta>'=\<theta>(t \<mapsto> ret (m a) (f (\<theta>(t \<mapsto> (m a)))))" and
	sb: "sb=[]" and
	sb': "sb' = []" and
	cond: "cond (\<theta>(t \<mapsto> m a))" 
	by auto


      from sim_loc [rule_format, OF i_bound] ts_i sb "is"
      obtain sb\<^sub>h \<O>\<^sub>h \<R>\<^sub>h \<D>\<^sub>h acq\<^sub>h where 
	ts\<^sub>h_i: "ts\<^sub>h!i = (p,RMW a t (D, f) cond ret A L R W# is',\<theta>,sb\<^sub>h,\<D>\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h)" and
	sb: "[] = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h"
	by (auto simp add: Let_def)

      from filter_is_Write\<^sub>s\<^sub>b_empty [OF sb [symmetric]]
      have "\<forall>r \<in> set sb\<^sub>h. is_Read\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r".

      from flush_reads_program [OF this] obtain \<O>\<^sub>h' \<S>\<^sub>h' \<R>\<^sub>h'
      where flsh: "(m, sb\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>f\<^sup>* (m, [],\<O>\<^sub>h',\<R>\<^sub>h',\<S>\<^sub>h')" by blast

      let ?ts\<^sub>h' = "ts\<^sub>h[i := (p,RMW a t (D, f) cond ret A L R W# is',\<theta>, [], \<D>\<^sub>h, \<O>\<^sub>h',\<R>\<^sub>h')]"

      from sbh_computation.store_buffer_steps [OF flsh i_bound' ts\<^sub>h_i]
      have "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (?ts\<^sub>h', m, \<S>\<^sub>h')".

      also

      from i_bound' have i_bound'': "i < length ?ts\<^sub>h'"
	by auto

      from i_bound' have ts\<^sub>h'_i: "?ts\<^sub>h'!i = (p,RMW a t (D, f) cond ret A L R W#is',\<theta>,[],\<D>\<^sub>h,\<O>\<^sub>h',\<R>\<^sub>h')"
	by simp

      note step= SBHRMWWrite [where cond=cond and \<theta>=\<theta> and m=m, OF cond] 
      from sbh_computation.Memop [OF i_bound'' ts\<^sub>h'_i step ] i_bound' 
      have "(?ts\<^sub>h', m, \<S>\<^sub>h') \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h (ts\<^sub>h[i := (p, is',
	     \<theta>(t \<mapsto> ret (m a) (f (\<theta>(t \<mapsto> (m a))))), [], False, \<O>\<^sub>h' \<union> A - R,Map.empty)],
	     m(a := f (\<theta>(t \<mapsto> (m a)))),\<S>\<^sub>h' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	by (simp)
      finally
      have "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>h[i := (p, is',
	     \<theta>(t \<mapsto> ret (m a) (f (\<theta>(t \<mapsto> (m a))))), [], False, \<O>\<^sub>h' \<union> A - R,Map.empty)],
            m(a := f (\<theta>(t \<mapsto> (m a)))),\<S>\<^sub>h' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

      moreover
    
      have "ts [i := (p,is',\<theta>(t \<mapsto> ret (m a) (f (\<theta>(t \<mapsto> (m a))))),[],\<D>,\<O>,\<R>)] \<sim>\<^sub>h 
            ts\<^sub>h[i := (p,is',\<theta>(t \<mapsto> ret (m a) (f (\<theta>(t \<mapsto> (m a))))), [],False, \<O>\<^sub>h' \<union> A - R,Map.empty)]"
	apply (rule sim_history_config.intros)
	using lts_eq
	apply  simp
	using sim_loc i_bound i_bound' sb 
	apply (auto simp add: Let_def nth_list_update)
	done

      ultimately show ?thesis
	by (auto simp add: ts' \<O>' \<theta>' m' sb' \<D>' \<S>' \<R>')
    next
      case (SBGhost A L R W)
      then obtain
	"is": "is = Ghost A L R W#is'" and
	\<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
	\<S>': "\<S>'=\<S>" and
	\<D>': "\<D>'=\<D>" and
	m': "m'=m" and
	\<theta>': "\<theta>'=\<theta>" and
	sb': "sb' = sb" 
	by auto

      from sim_loc [rule_format, OF i_bound] ts_i  "is"
      obtain sb\<^sub>h \<O>\<^sub>h \<R>\<^sub>h \<D>\<^sub>h where 
	ts\<^sub>h_i: "ts\<^sub>h!i = (p,Ghost A L R W# is',\<theta>,sb\<^sub>h,\<D>\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h)" and
	sb: "sb = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h" and
        sb_empty: "filter is_Write\<^sub>s\<^sub>b sb\<^sub>h = [] \<longrightarrow> sb\<^sub>h=[]"
	by (auto simp add: Let_def)

      let ?ts\<^sub>h_i' = "(p, is', \<theta>, sb\<^sub>h@[Ghost\<^sub>s\<^sub>b A L R W],\<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)"
      let ?ts\<^sub>h' = "ts\<^sub>h[i := ?ts\<^sub>h_i']" 
      note step= SBHGhost  
      from sbh_computation.Memop [OF i_bound' ts\<^sub>h_i step ] i_bound' 
      have step: "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h (?ts\<^sub>h',m, \<S>\<^sub>h)"
	by (simp)

      from sb have sb: "sb = filter is_Write\<^sub>s\<^sub>b (sb\<^sub>h @ [Ghost\<^sub>s\<^sub>b A L R W])"
	by simp

      show ?thesis
      proof (cases "filter is_Write\<^sub>s\<^sub>b sb\<^sub>h = []")
        case False

        have "ts [i := (p,is',\<theta>,sb,\<D>,\<O>,\<R>)] \<sim>\<^sub>h ?ts\<^sub>h'"
	  apply (rule sim_history_config.intros)
	  using lts_eq
	  apply  simp
	  using sim_loc i_bound i_bound' sb sb_empty False
	  apply (auto simp add: Let_def nth_list_update)
	  done

        with step show ?thesis
	  by (auto simp del: fun_upd_apply simp add: \<S>' m' ts' \<O>' \<D>' \<theta>' sb' \<R>')
      next
        case True
        with sb_empty have empty: "sb\<^sub>h=[]" by simp
        from i_bound' have "?ts\<^sub>h'!i = ?ts\<^sub>h_i'"
          by auto
        from sbh_computation.StoreBuffer [OF _ this, simplified empty, simplified, OF _ flush_step.Ghost, of m \<S>\<^sub>h] i_bound'
        have "(?ts\<^sub>h', m, \<S>\<^sub>h)
              \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h  (ts\<^sub>h[i := (p, is', \<theta>, [], \<D>\<^sub>h, \<O>\<^sub>h \<union> A - R,augment_rels (dom \<S>\<^sub>h) R \<R>\<^sub>h)], m, \<S>\<^sub>h \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
          by (simp add: empty)
        with step have "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>*
              (ts\<^sub>h[i := (p, is', \<theta>, [], \<D>\<^sub>h, \<O>\<^sub>h \<union> A - R,augment_rels (dom \<S>\<^sub>h) R \<R>\<^sub>h)], m, \<S>\<^sub>h \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
          by force
        moreover
        have "ts [i := (p,is',\<theta>,sb,\<D>,\<O>,\<R>)] \<sim>\<^sub>h 
                 ts\<^sub>h[i := (p, is', \<theta>, [], \<D>\<^sub>h, \<O>\<^sub>h \<union> A - R,augment_rels (dom \<S>\<^sub>h) R \<R>\<^sub>h)]"
          apply (rule sim_history_config.intros)
	  using lts_eq
	  apply  simp
	  using sim_loc i_bound i_bound' sb empty 
	  apply (auto simp add: Let_def nth_list_update)
	  done
        ultimately show ?thesis
	  by (auto simp del: fun_upd_apply simp add: \<S>' m' ts' \<O>' \<theta>' \<D>' sb' \<R>')
      qed
    qed
  next
    case (Program i _ p "is" \<theta> sb \<D> \<O> \<R> p' "is'")
    then obtain 
      ts': "ts' = ts[i := (p', is@is',\<theta>, sb, \<D>, \<O>,\<R>)]" and
      i_bound: "i < length ts" and
      ts_i: "ts ! i = (p, is, \<theta>,sb,\<D>, \<O>,\<R>)" and
      prog_step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>p (p', is')" and
      \<S>': "\<S>'=\<S>" and
      m': "m'=m"
      by auto

    from sim obtain 
      lts_eq: "length ts = length ts\<^sub>h" and
      sim_loc: "\<forall>i < length ts. (\<exists>\<O>' \<D>' \<R>'. 
            let (p,is,\<theta>, sb, \<D>, \<O>,\<R>) = ts\<^sub>h!i in ts!i=(p,is, \<theta>, filter is_Write\<^sub>s\<^sub>b sb,\<D>',\<O>',\<R>') \<and>
                (filter is_Write\<^sub>s\<^sub>b sb = [] \<longrightarrow> sb = []))"
      by cases auto

    from sim_loc [rule_format, OF i_bound] ts_i 
      obtain sb\<^sub>h \<O>\<^sub>h \<R>\<^sub>h \<D>\<^sub>h acq\<^sub>h where 
	ts\<^sub>h_i: "ts\<^sub>h!i = (p,is,\<theta>,sb\<^sub>h,\<D>\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h)" and
	sb: "sb = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h" and
        sb_empty: "filter is_Write\<^sub>s\<^sub>b sb\<^sub>h = [] \<longrightarrow> sb\<^sub>h=[]"
	by (auto simp add: Let_def)

    from lts_eq i_bound have i_bound': "i < length ts\<^sub>h"
      by simp
   
    let ?ts\<^sub>h_i' = "(p', is @ is',\<theta>, sb\<^sub>h @ [Prog\<^sub>s\<^sub>b p p' is'], \<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)"
      let ?ts\<^sub>h' = "ts\<^sub>h[i := ?ts\<^sub>h_i']" 
    from sbh_computation.Program [OF i_bound' ts\<^sub>h_i prog_step]
    have step: "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h (?ts\<^sub>h',m, \<S>\<^sub>h)".
    
    show ?thesis
    proof (cases "filter is_Write\<^sub>s\<^sub>b sb\<^sub>h = []")
      case False
      have "ts[i := (p', is@is', \<theta>, sb,\<D>, \<O>,\<R>)] \<sim>\<^sub>h ?ts\<^sub>h'"
        apply (rule sim_history_config.intros)
        using lts_eq
        apply  simp
        using sim_loc i_bound i_bound' sb False sb_empty
        apply (auto simp add: Let_def nth_list_update)
        done
      
      with step show ?thesis
        by (auto simp add: ts' \<S>' m')
    next
      case True
      with sb_empty have empty: "sb\<^sub>h=[]" by simp
      from i_bound' have "?ts\<^sub>h'!i = ?ts\<^sub>h_i'"
        by auto
      
      from sbh_computation.StoreBuffer [OF _ this, simplified empty, simplified, OF _ flush_step.Prog\<^sub>s\<^sub>b, of m \<S>\<^sub>h] i_bound'
      have "(?ts\<^sub>h', m, \<S>\<^sub>h)
              \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h  (ts\<^sub>h[i := (p', is@is', \<theta>, [], \<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)], m, \<S>\<^sub>h)"
        by (simp add: empty)
      with step have "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>*
           (ts\<^sub>h[i := (p', is@is', \<theta>, [], \<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)], m, \<S>\<^sub>h) "
        by force
      moreover
      have "ts[i := (p', is@is', \<theta>, sb,\<D>, \<O>,\<R>)] \<sim>\<^sub>h ts\<^sub>h[i := (p', is@is', \<theta>, [], \<D>\<^sub>h, \<O>\<^sub>h,\<R>\<^sub>h)]"
        apply (rule sim_history_config.intros)
	using lts_eq
	apply  simp
	using sim_loc i_bound i_bound' sb empty 
	apply (auto simp add: Let_def nth_list_update)
	done
      ultimately show ?thesis
        by (auto simp del: fun_upd_apply simp add: \<S>' m' ts')
    qed
  next
    case (StoreBuffer i _ p "is" \<theta> sb \<D> \<O> \<R>  _ _ _ sb' \<O>' \<R>')
    then obtain 
      ts': "ts' = ts[i := (p, is,\<theta>, sb', \<D>, \<O>',\<R>')]" and
      i_bound: "i < length ts" and
      ts_i: "ts ! i = (p, is,\<theta>,sb, \<D>, \<O>,\<R>)" and
      sb_step: "(m,sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>w (m', sb',\<O>',\<R>',\<S>')" 
      by auto

    from sim obtain
      lts_eq: "length ts = length ts\<^sub>h" and
      sim_loc: "\<forall>i < length ts. (\<exists>\<O>' \<D>' \<R>'. 
            let (p,is, \<theta>, sb,\<D>, \<O>,\<R>) = ts\<^sub>h!i in ts!i=(p,is, \<theta>, filter is_Write\<^sub>s\<^sub>b sb,\<D>',\<O>',\<R>') \<and>
                (filter is_Write\<^sub>s\<^sub>b sb = [] \<longrightarrow> sb=[]))"
      by cases auto

    from sim_loc [rule_format, OF i_bound] ts_i 
      obtain sb\<^sub>h \<O>\<^sub>h \<R>\<^sub>h \<D>\<^sub>h acq\<^sub>h where 
	ts\<^sub>h_i: "ts\<^sub>h!i = (p,is,\<theta>,sb\<^sub>h,\<D>\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h)" and
	sb: "sb = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h" and        
        sb_empty: "filter is_Write\<^sub>s\<^sub>b sb\<^sub>h = [] \<longrightarrow> sb\<^sub>h=[]"
	by (auto simp add: Let_def)

    from lts_eq i_bound have i_bound': "i < length ts\<^sub>h"
      by simp

    from flush_simulates_filter_writes [OF sb_step sb, of \<O>\<^sub>h \<R>\<^sub>h \<S>\<^sub>h] 
    obtain sb\<^sub>h' \<O>\<^sub>h' \<R>\<^sub>h' \<S>\<^sub>h' 
      where flush': "(m, sb\<^sub>h,\<O>\<^sub>h,\<R>\<^sub>h,\<S>\<^sub>h) \<rightarrow>\<^sub>f\<^sup>* (m', sb\<^sub>h',\<O>\<^sub>h',\<R>\<^sub>h',\<S>\<^sub>h')" and 
      sb': "sb' = filter is_Write\<^sub>s\<^sub>b sb\<^sub>h'" and
      sb'_empty: "filter is_Write\<^sub>s\<^sub>b sb\<^sub>h' = [] \<longrightarrow> sb\<^sub>h'=[]"
      by auto

    from sb_step obtain volatile a sop v A L R W where "sb=Write\<^sub>s\<^sub>b volatile a sop v A L R W#sb'"
      by cases force
    from sbh_computation.store_buffer_steps [OF flush' i_bound' ts\<^sub>h_i]
    have "(ts\<^sub>h, m, \<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>h[i := (p, is, \<theta>, sb\<^sub>h',\<D>\<^sub>h, \<O>\<^sub>h',\<R>\<^sub>h')], m', \<S>\<^sub>h')".
    
    moreover
    have "ts[i := (p, is, \<theta>, sb',\<D>, \<O>',\<R>')] \<sim>\<^sub>h 
          ts\<^sub>h[i := (p, is, \<theta>, sb\<^sub>h',\<D>\<^sub>h, \<O>\<^sub>h',\<R>\<^sub>h')]"
      apply (rule sim_history_config.intros)
      using lts_eq
      apply  simp
      using sim_loc i_bound i_bound' sb sb' sb'_empty
      apply (auto simp add: Let_def nth_list_update)
      done

    ultimately show ?thesis
      by (auto simp add: ts' )
  qed
qed



theorem (in valid_program) concurrent_history_steps_simulates_store_buffer_steps:
  assumes step_sb: "(ts,m,\<S>) \<Rightarrow>\<^sub>s\<^sub>b\<^sup>*  (ts',m',\<S>')"
  shows "\<And>ts\<^sub>h \<S>\<^sub>h. ts \<sim>\<^sub>h ts\<^sub>h \<Longrightarrow> \<exists>ts\<^sub>h' \<S>\<^sub>h'. (ts\<^sub>h,m,\<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>h',m',\<S>\<^sub>h') \<and> ts' \<sim>\<^sub>h ts\<^sub>h'"
using step_sb
proof (induct rule: converse_rtranclp_induct_sbh_steps) 
  case refl thus ?case by auto
next
  case (step ts m \<S>  ts'' m'' \<S>'' )
  have first: "(ts,m,\<S>) \<Rightarrow>\<^sub>s\<^sub>b  (ts'',m'',\<S>'')" by fact
  have sim: "ts \<sim>\<^sub>h ts\<^sub>h" by fact
  from concurrent_history_steps_simulates_store_buffer_step [OF first sim, of \<S>\<^sub>h]
  obtain ts\<^sub>h'' \<S>\<^sub>h'' where
    exec: "(ts\<^sub>h,m,\<S>\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>h'',m'',\<S>\<^sub>h'')" and  sim: "ts'' \<sim>\<^sub>h ts\<^sub>h''"
    by auto
  from step.hyps (3) [OF sim, of \<S>\<^sub>h'']
  obtain ts\<^sub>h' \<S>\<^sub>h' where exec_rest: "(ts\<^sub>h'',m'',\<S>\<^sub>h'')  \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>h',m',\<S>\<^sub>h')" and sim': "ts' \<sim>\<^sub>h ts\<^sub>h'"
    by auto
  note exec also note exec_rest
  finally show ?case
  using sim' by blast
qed

theorem (in xvalid_program_progress) concurrent_direct_execution_simulates_store_buffer_execution:
assumes exec_sb: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,x) \<Rightarrow>\<^sub>s\<^sub>b\<^sup>* (ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b',x')"
assumes init: "initial\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b"
assumes valid: "valid ts\<^sub>s\<^sub>b" (* FIXME: move into initial ?*)
assumes sim: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<sim> (ts,m,\<S>)"
assumes safe: "safe_reach_direct safe_free_flowing (ts,m,\<S>)"
shows "\<exists>ts\<^sub>h' \<S>\<^sub>h' ts' m' \<S>'. 
          (ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>h',m\<^sub>s\<^sub>b',\<S>\<^sub>h') \<and>
               ts\<^sub>s\<^sub>b' \<sim>\<^sub>h ts\<^sub>h' \<and>
          (ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>') \<and> 
                (ts\<^sub>h',m\<^sub>s\<^sub>b',\<S>\<^sub>h') \<sim> (ts',m',\<S>')"
proof -
  from init interpret ini: initial\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b .
  from concurrent_history_steps_simulates_store_buffer_steps [OF exec_sb ini.history_refl, of \<S>\<^sub>s\<^sub>b]
  obtain ts\<^sub>h' \<S>\<^sub>h' where
    sbh: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>h',m\<^sub>s\<^sub>b',\<S>\<^sub>h')" and
    sim_sbh: "ts\<^sub>s\<^sub>b' \<sim>\<^sub>h ts\<^sub>h'"
    by auto
  from concurrent_direct_execution_simulates_store_buffer_history_execution [OF sbh init valid sim safe]
  obtain ts' m' \<S>' where
    d: "(ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>')" and
    d_sim: "(ts\<^sub>h',m\<^sub>s\<^sub>b',\<S>\<^sub>h') \<sim> (ts',m',\<S>')"
    by auto
  with sbh sim_sbh show ?thesis by blast
qed

  

inductive sim_direct_config:: 
 "('p,'p store_buffer,'dirty,'owns,'rels) thread_config list \<Rightarrow> ('p,unit,bool,'owns','rels') thread_config list \<Rightarrow> bool" 
  ("_ \<sim>\<^sub>d _ " [60,60] 100)
where
  "\<lbrakk>length ts = length ts\<^sub>d; 
    \<forall>i < length ts. 
         (\<exists>\<O>' \<D>' \<R>'.
           let (p,is, \<theta>,sb,\<D>, \<O>,\<R>) = ts\<^sub>d!i in 
                ts!i=(p,is, \<theta>, [] ,\<D>',\<O>',\<R>'))
   \<rbrakk> 
    \<Longrightarrow> 
     ts \<sim>\<^sub>d ts\<^sub>d"

lemma empty_sb_sims: 
assumes empty:
  "\<forall>i p is xs sb \<D> \<O> \<R>. i < length ts\<^sub>s\<^sub>b \<longrightarrow> ts\<^sub>s\<^sub>b!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<longrightarrow> sb=[]"
assumes sim_h: "ts\<^sub>s\<^sub>b \<sim>\<^sub>h ts\<^sub>h"
assumes sim_d: "(ts\<^sub>h,m\<^sub>h,\<S>\<^sub>h) \<sim> (ts,m,\<S>)"
shows "ts\<^sub>s\<^sub>b \<sim>\<^sub>d ts \<and> m\<^sub>h=m \<and> length ts\<^sub>s\<^sub>b = length ts"
proof-
  from sim_h empty
  have empty':
  "\<forall>i p is xs sb \<D> \<O> \<R>. i < length ts\<^sub>h \<longrightarrow> ts\<^sub>h!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<longrightarrow> sb=[]"
    apply (cases)
    apply clarsimp
    subgoal for i
    apply (drule_tac x=i in spec)
    apply (auto simp add: Let_def)
    done
    done
  from sim_h sim_config_emptyE [OF empty' sim_d]
  show ?thesis
    apply cases
    apply clarsimp
    apply (rule sim_direct_config.intros)
    apply  clarsimp
    apply clarsimp
    using empty'
    subgoal for i
    apply (drule_tac x=i in spec)
    apply (drule_tac x=i in spec)
    apply (drule_tac x=i in spec)
    apply (auto simp add: Let_def)
    done
    done
qed

lemma empty_d_sims:
assumes sim: "ts\<^sub>s\<^sub>b \<sim>\<^sub>d ts"
shows "\<exists>ts\<^sub>h. ts\<^sub>s\<^sub>b \<sim>\<^sub>h ts\<^sub>h \<and> (ts\<^sub>h,m,\<S>) \<sim> (ts,m,\<S>)"
proof -
  from sim obtain
    leq: "length ts\<^sub>s\<^sub>b = length ts" and
    sim: "\<forall>i < length ts\<^sub>s\<^sub>b. 
         (\<exists>\<O>' \<D>' \<R>'.
           let (p,is, \<theta>,sb,\<D>, \<O>,\<R>) = ts!i in 
                ts\<^sub>s\<^sub>b!i=(p,is, \<theta>, [] ,\<D>',\<O>',\<R>'))"
    by cases auto
  define ts\<^sub>h where "ts\<^sub>h \<equiv> map (\<lambda>(p,is, \<theta>,sb,\<D>, \<O>,\<R>). (p,is, \<theta>,[]::'a memref list,\<D>, \<O>,\<R>)) ts" 
  have "ts\<^sub>s\<^sub>b \<sim>\<^sub>h ts\<^sub>h"
    apply (rule sim_history_config.intros)
    using leq sim
    apply (auto simp add: ts\<^sub>h_def Let_def leq)
    done
  moreover
  have empty:
  "\<forall>i p is xs sb \<D> \<O> \<R>. i < length ts\<^sub>h \<longrightarrow> ts\<^sub>h!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<longrightarrow> sb=[]"
    apply (clarsimp simp add: ts\<^sub>h_def Let_def)
    subgoal for i
    apply (case_tac "ts!i")
    apply auto
    done
    done
  
  have "(ts\<^sub>h,m,\<S>) \<sim> (ts,m,\<S>)"
    apply (rule sim_config_emptyI [OF empty])
    apply  (clarsimp simp add: ts\<^sub>h_def)
    apply (clarsimp simp add: ts\<^sub>h_def Let_def)
    subgoal for i
    apply (case_tac "ts!i")
    apply auto
    done
    done
  ultimately show ?thesis by blast
qed


theorem (in xvalid_program_progress) concurrent_direct_execution_simulates_store_buffer_execution_empty:
assumes exec_sb: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,x) \<Rightarrow>\<^sub>s\<^sub>b\<^sup>* (ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b',x')"
assumes init: "initial\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b"
assumes valid: "valid ts\<^sub>s\<^sub>b" (* FIXME: move into initial ?*)
assumes empty: 
  "\<forall>i p is xs sb \<D> \<O> \<R>. i < length ts\<^sub>s\<^sub>b' \<longrightarrow> ts\<^sub>s\<^sub>b'!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<longrightarrow> sb=[]"
assumes sim: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<sim> (ts,m,\<S>)"
assumes safe: "safe_reach_direct safe_free_flowing (ts,m,\<S>)"
shows "\<exists>ts' \<S>'. 
          (ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m\<^sub>s\<^sub>b',\<S>') \<and> ts\<^sub>s\<^sub>b' \<sim>\<^sub>d ts'"
proof -
  from concurrent_direct_execution_simulates_store_buffer_execution [OF exec_sb init valid sim safe]
  obtain ts\<^sub>h' \<S>\<^sub>h' ts' m' \<S>' where
    "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>h',m\<^sub>s\<^sub>b',\<S>\<^sub>h')" and
    sim_h: "ts\<^sub>s\<^sub>b' \<sim>\<^sub>h ts\<^sub>h'" and
    exec: "(ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>')" and
    sim: "(ts\<^sub>h',m\<^sub>s\<^sub>b',\<S>\<^sub>h') \<sim> (ts',m',\<S>')"
    by auto
  from empty_sb_sims [OF empty sim_h sim]
  obtain "ts\<^sub>s\<^sub>b' \<sim>\<^sub>d ts'" "m\<^sub>s\<^sub>b' = m'" "length ts\<^sub>s\<^sub>b' = length ts'"
    by auto
  thus ?thesis
    using exec
    by blast
qed

locale initial\<^sub>d = simple_ownership_distinct + read_only_unowned + unowned_shared +
fixes valid
assumes empty_is: "\<lbrakk>i < length ts; ts!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<rbrakk> \<Longrightarrow> is=[]"
assumes empty_rels: "\<lbrakk>i < length ts; ts!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<rbrakk> \<Longrightarrow> \<R>=Map.empty"
assumes valid_init: "valid (map (\<lambda>(p,is, \<theta>,sb,\<D>, \<O>,\<R>). (p,is, \<theta>,[],\<D>, \<O>,\<R>)) ts)"

locale empty_store_buffers =
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes empty_sb: "\<lbrakk>i < length ts; ts!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<rbrakk> \<Longrightarrow> sb=[]"

lemma initial_d_sb:
  assumes init: "initial\<^sub>d ts \<S> valid"
  shows "initial\<^sub>s\<^sub>b (map (\<lambda>(p,is, \<theta>,sb,\<D>, \<O>,\<R>). (p,is, \<theta>,[],\<D>, \<O>,\<R>)) ts) \<S>" 
         (is "initial\<^sub>s\<^sub>b ?map \<S>")
proof -
  from init interpret ini: initial\<^sub>d ts \<S> .
  show ?thesis
  proof (intro_locales)
    show "simple_ownership_distinct ?map"
    apply (clarsimp simp add: simple_ownership_distinct_def)
    subgoal for i j
    apply (case_tac "ts!i")
    apply (case_tac "ts!j")
    apply (cut_tac i=i and j=j in ini.simple_ownership_distinct)
    apply      clarsimp
    apply     clarsimp
    apply    clarsimp
    apply   assumption
    apply  assumption
    apply auto
    done
    done
  next
    show "read_only_unowned \<S> ?map"
    apply (clarsimp simp add: read_only_unowned_def)
    subgoal for i
    apply (case_tac "ts!i")
    apply (cut_tac i=i in ini.read_only_unowned)
    apply   clarsimp
    apply  assumption
    apply auto
    done
    done
  next
    show "unowned_shared \<S> ?map"
    apply (clarsimp simp add: unowned_shared_def')
    apply (rule ini.unowned_shared')
    apply clarsimp
    subgoal for a i
    apply (case_tac "ts!i")
    apply auto
    done
    done
  next
    show "initial\<^sub>s\<^sub>b_axioms ?map"
    apply (unfold_locales)
            subgoal for i
            apply (case_tac "ts!i")
            apply simp
            done
           subgoal for i
           apply  (case_tac "ts!i")
           apply  clarsimp
           apply  (rule_tac i=i in ini.empty_is)
           apply   clarsimp
           apply  fastforce
           done
    subgoal for i
    apply (case_tac "ts!i")
    apply clarsimp
    apply (rule_tac i=i in ini.empty_rels)
    apply  clarsimp
    apply fastforce
    done
    done
  qed
qed

theorem (in xvalid_program_progress) store_buffer_execution_result_sequential_consistent:
assumes exec_sb: "(ts\<^sub>s\<^sub>b,m,x) \<Rightarrow>\<^sub>s\<^sub>b\<^sup>* (ts\<^sub>s\<^sub>b',m',x')"
assumes empty': "empty_store_buffers ts\<^sub>s\<^sub>b'"
assumes sim: "ts\<^sub>s\<^sub>b \<sim>\<^sub>d ts"
assumes init: "initial\<^sub>d ts \<S> valid"
assumes safe: "safe_reach_direct safe_free_flowing (ts,m,\<S>)"
shows "\<exists>ts' \<S>'. 
          (ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>') \<and> ts\<^sub>s\<^sub>b' \<sim>\<^sub>d ts'"
proof -
  from empty'
  have empty': 
  "\<forall>i p is xs sb \<D> \<O> \<R>. i < length ts\<^sub>s\<^sub>b' \<longrightarrow> ts\<^sub>s\<^sub>b'!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<longrightarrow> sb=[]"
    by (auto simp add: empty_store_buffers_def)

  define ts\<^sub>h where "ts\<^sub>h \<equiv> map (\<lambda>(p,is, \<theta>,sb,\<D>, \<O>,\<R>). (p,is, \<theta>,[]::'a memref list,\<D>, \<O>,\<R>)) ts" 
  from initial_d_sb [OF init]
  have init_h:"initial\<^sub>s\<^sub>b ts\<^sub>h \<S>"
    by (simp add: ts\<^sub>h_def)
  from initial\<^sub>d.valid_init [OF init]
  have valid_h: "valid ts\<^sub>h"
    by (simp add: ts\<^sub>h_def)
  from sim obtain
    leq: "length ts\<^sub>s\<^sub>b = length ts" and
    sim: "\<forall>i < length ts\<^sub>s\<^sub>b. 
         (\<exists>\<O>' \<D>' \<R>'.
           let (p,is, \<theta>,sb,\<D>, \<O>,\<R>) = ts!i in 
                ts\<^sub>s\<^sub>b!i=(p,is, \<theta>, [] ,\<D>',\<O>',\<R>'))"
    by cases auto
  have sim_h: "ts\<^sub>s\<^sub>b \<sim>\<^sub>h ts\<^sub>h"
    apply (rule sim_history_config.intros)
    using leq sim
    apply (auto simp add: ts\<^sub>h_def Let_def leq)
    done

  from concurrent_history_steps_simulates_store_buffer_steps [OF exec_sb sim_h, of \<S>]
  obtain ts\<^sub>h' \<S>\<^sub>h' where steps_h: "(ts\<^sub>h,m,\<S>) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>h',m',\<S>\<^sub>h')" and
     sim_h': "ts\<^sub>s\<^sub>b' \<sim>\<^sub>h ts\<^sub>h'"
    by auto

  moreover
  have empty:
  "\<forall>i p is xs sb \<D> \<O> \<R>. i < length ts\<^sub>h \<longrightarrow> ts\<^sub>h!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<longrightarrow> sb=[]"
    apply (clarsimp simp add: ts\<^sub>h_def Let_def)
    subgoal for i
    apply (case_tac "ts!i")
    apply auto
    done
    done
  
  have sim': "(ts\<^sub>h,m,\<S>) \<sim> (ts,m,\<S>)"
    apply (rule sim_config_emptyI [OF empty])
    apply  (clarsimp simp add: ts\<^sub>h_def)
    apply (clarsimp simp add: ts\<^sub>h_def Let_def)
    subgoal for i
    apply (case_tac "ts!i")
    apply auto
    done
  done

  from concurrent_direct_execution_simulates_store_buffer_history_execution [OF steps_h init_h valid_h sim' safe]
  obtain ts' m'' \<S>'' where steps: "(ts, m, \<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts', m'', \<S>'')" 
    and sim': "(ts\<^sub>h', m', \<S>\<^sub>h') \<sim> (ts', m'', \<S>'')"
    by blast
  from empty_sb_sims [OF empty' sim_h' sim'] steps
  show ?thesis
    by auto
qed


locale initial\<^sub>v = simple_ownership_distinct + read_only_unowned + unowned_shared +
fixes valid
assumes empty_is: "\<lbrakk>i < length ts; ts!i=(p,is,xs,sb,\<D>,\<O>,\<R>)\<rbrakk> \<Longrightarrow> is=[]"
assumes valid_init: "valid (map (\<lambda>(p,is, \<theta>,sb,\<D>, \<O>,\<R>). (p,is, \<theta>,[],\<D>, \<O>,Map.empty)) ts)"

(*
term "initial\<^sub>v"
context xvalid_program_progress
begin
term "safe_reach safe_free_flowing (ts,m,\<S>)"
theorem (in xvalid_program_progress) store_buffer_execution_result_sequential_consistent':
assumes exec_sb: "(ts\<^sub>s\<^sub>b,m,x) \<Rightarrow>\<^sub>s\<^sub>b\<^sup>* (ts\<^sub>s\<^sub>b',m',x')"
assumes sim: "ts\<^sub>s\<^sub>b \<sim>\<^sub>d ts"

assumes safe: " safe_reach safe_free_flowing (ts,m,\<S>)"
shows "\<exists>ts' \<S>'. 
          (ts,m,\<S>) \<Rightarrow>\<^sub>v\<^sup>* (ts',m',\<S>') "
*)



theorem (in xvalid_program_progress) store_buffer_execution_result_sequential_consistent':
assumes exec_sb: "(ts\<^sub>s\<^sub>b,m,x) \<Rightarrow>\<^sub>s\<^sub>b\<^sup>* (ts\<^sub>s\<^sub>b',m',x')"
assumes empty': "empty_store_buffers ts\<^sub>s\<^sub>b'"
assumes sim: "ts\<^sub>s\<^sub>b \<sim>\<^sub>d ts"
assumes init: "initial\<^sub>v ts \<S> valid"
assumes safe: "safe_reach_virtual safe_free_flowing (ts,m,\<S>)"
shows "\<exists>ts' \<S>'. 
          (ts,m,\<S>) \<Rightarrow>\<^sub>v\<^sup>* (ts',m',\<S>') \<and> ts\<^sub>s\<^sub>b' \<sim>\<^sub>d ts'"
proof -
  define ts\<^sub>d where "ts\<^sub>d == (map (\<lambda>(p,is, \<theta>,sb,\<D>, \<O>,\<R>'). (p,is, \<theta>,sb,\<D>, \<O>,Map.empty::rels)) ts)"
  have rem_ts: "remove_rels ts\<^sub>d = ts"
    apply (rule nth_equalityI)
    apply  (simp add: ts\<^sub>d_def remove_rels_def)
    apply (clarsimp simp add: ts\<^sub>d_def remove_rels_def)
    subgoal for i
    apply (case_tac "ts!i")
    apply clarsimp
    done
    done
  from sim
  have sim': "ts\<^sub>s\<^sub>b \<sim>\<^sub>d ts\<^sub>d"
    apply cases
    apply (rule sim_direct_config.intros)
    apply (auto simp add: ts\<^sub>d_def)
    done
  
  have init': "initial\<^sub>d ts\<^sub>d \<S> valid"
  proof (intro_locales)
    from init have "simple_ownership_distinct ts"
      by (simp add: initial\<^sub>v_def)
    then
    show "simple_ownership_distinct ts\<^sub>d"
      apply (clarsimp simp add: ts\<^sub>d_def simple_ownership_distinct_def)
      subgoal for i j
      apply (case_tac "ts!i")
      apply (case_tac "ts!j")
      apply force
      done
      done
  next
    from init have "read_only_unowned \<S> ts"
      by (simp add: initial\<^sub>v_def)
    then show "read_only_unowned \<S> ts\<^sub>d"
      apply (clarsimp simp add: ts\<^sub>d_def read_only_unowned_def)
      subgoal for i
      apply (case_tac "ts!i")
      apply force
      done
      done
  next
    from init have "unowned_shared \<S> ts"
      by (simp add: initial\<^sub>v_def)
    then 
    show "unowned_shared \<S> ts\<^sub>d"
      apply (clarsimp simp add: ts\<^sub>d_def unowned_shared_def)
      apply force
      done
  next
    have eq: "((\<lambda>(p, is, \<theta>, sb, \<D>, \<O>, \<R>). (p, is, \<theta>, [], \<D>, \<O>, \<R>)) \<circ>
              (\<lambda>(p, is, \<theta>, sb, \<D>, \<O>, \<R>'). (p, is, \<theta>, (), \<D>, \<O>, Map.empty))) 
     = (\<lambda>(p, is, \<theta>, sb, \<D>, \<O>, \<R>'). (p, is, \<theta>, [], \<D>, \<O>, Map.empty))"
      apply (rule ext)
      subgoal for x
      apply (case_tac x)
      apply auto
      done
      done
    from init have "initial\<^sub>v_axioms ts valid"
      by (simp add: initial\<^sub>v_def)
     
    then
    show "initial\<^sub>d_axioms ts\<^sub>d valid"
      apply (clarsimp simp add: ts\<^sub>d_def initial\<^sub>v_axioms_def initial\<^sub>d_axioms_def eq)
      apply (rule conjI)
      apply  clarsimp
             subgoal for i
             apply (case_tac "ts!i")
             apply force
             done
      apply clarsimp
      subgoal for i
      apply (case_tac "ts!i")
      apply force
      done
      done
  qed

  {
    fix ts\<^sub>d' m' \<S>'
    assume exec: "(ts\<^sub>d, m, \<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts\<^sub>d', m', \<S>')"
    have "safe_free_flowing (ts\<^sub>d', m', \<S>')"
    proof -
      from virtual_simulates_direct_steps [OF exec]
      have exec_v: "(ts, m, \<S>) \<Rightarrow>\<^sub>v\<^sup>* (remove_rels ts\<^sub>d', m', \<S>')"
        by (simp add: rem_ts)
      have eq: "map (owned \<circ>
                    (\<lambda>(p, is, \<theta>, sb, \<D>, \<O>, \<R>). (p, is, \<theta>, (), \<D>, \<O>, ())))
                ts\<^sub>d' = map owned ts\<^sub>d'"
        by auto
      from exec_v safe
      have "safe_free_flowing (remove_rels ts\<^sub>d', m', \<S>')"
        by (auto simp add: safe_reach_def)
      then show ?thesis
        by (auto simp add: safe_free_flowing_def remove_rels_def owned_def eq)
    qed
  }
  hence safe': "safe_reach_direct safe_free_flowing (ts\<^sub>d, m, \<S>)"
    by (simp add: safe_reach_def)
          
  from store_buffer_execution_result_sequential_consistent [OF exec_sb empty' sim' init' safe'] 
  obtain ts\<^sub>d' \<S>' where
     exec_d: "(ts\<^sub>d, m, \<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts\<^sub>d', m', \<S>')"  and sim_d: "ts\<^sub>s\<^sub>b' \<sim>\<^sub>d ts\<^sub>d'"
    by blast

  from virtual_simulates_direct_steps [OF exec_d]
  have "(ts, m, \<S>) \<Rightarrow>\<^sub>v\<^sup>* (remove_rels ts\<^sub>d', m', \<S>')"
    by (simp add: rem_ts)
  moreover
  from sim_d
  have "ts\<^sub>s\<^sub>b' \<sim>\<^sub>d remove_rels ts\<^sub>d'"
    apply (cases)
    apply (rule sim_direct_config.intros)
    apply (auto simp add: remove_rels_def)
    done
  ultimately show ?thesis
    by auto
qed

subsection \<open>Plug Together the Two Simulations\<close>

corollary (in xvalid_program) concurrent_direct_steps_simulates_store_buffer_step:
  assumes step_sb: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<Rightarrow>\<^sub>s\<^sub>b (ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b')"
  assumes sim_h: "ts\<^sub>s\<^sub>b \<sim>\<^sub>h ts\<^sub>s\<^sub>b\<^sub>h"
  assumes sim: "(ts\<^sub>s\<^sub>b\<^sub>h,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b\<^sub>h) \<sim> (ts,m,\<S>) "
  assumes valid_own: "valid_ownership \<S>\<^sub>s\<^sub>b\<^sub>h ts\<^sub>s\<^sub>b\<^sub>h"
  assumes valid_sb_reads: "valid_reads m\<^sub>s\<^sub>b ts\<^sub>s\<^sub>b\<^sub>h"
  assumes valid_hist: "valid_history program_step ts\<^sub>s\<^sub>b\<^sub>h"
  assumes valid_sharing: "valid_sharing \<S>\<^sub>s\<^sub>b\<^sub>h ts\<^sub>s\<^sub>b\<^sub>h"
  assumes tmps_distinct: "tmps_distinct ts\<^sub>s\<^sub>b\<^sub>h"
  assumes valid_sops: "valid_sops ts\<^sub>s\<^sub>b\<^sub>h"
  assumes valid_dd: "valid_data_dependency ts\<^sub>s\<^sub>b\<^sub>h"
  assumes load_tmps_fresh: "load_tmps_fresh ts\<^sub>s\<^sub>b\<^sub>h"
  assumes enough_flushs: "enough_flushs ts\<^sub>s\<^sub>b\<^sub>h"
  assumes valid_program_history: "valid_program_history ts\<^sub>s\<^sub>b\<^sub>h"
  assumes valid: "valid ts\<^sub>s\<^sub>b\<^sub>h"
  assumes safe_reach: "safe_reach_direct safe_delayed (ts,m,\<S>)"
  shows "\<exists>ts\<^sub>s\<^sub>b\<^sub>h' \<S>\<^sub>s\<^sub>b\<^sub>h'. 
         (ts\<^sub>s\<^sub>b\<^sub>h,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>s\<^sub>b\<^sub>h',m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b\<^sub>h') \<and> ts\<^sub>s\<^sub>b' \<sim>\<^sub>h ts\<^sub>s\<^sub>b\<^sub>h' \<and>
         valid_ownership \<S>\<^sub>s\<^sub>b\<^sub>h' ts\<^sub>s\<^sub>b\<^sub>h' \<and> valid_reads m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b\<^sub>h' \<and> 
         valid_history program_step ts\<^sub>s\<^sub>b\<^sub>h' \<and>
         valid_sharing \<S>\<^sub>s\<^sub>b\<^sub>h' ts\<^sub>s\<^sub>b\<^sub>h' \<and> tmps_distinct ts\<^sub>s\<^sub>b\<^sub>h' \<and> valid_data_dependency ts\<^sub>s\<^sub>b\<^sub>h' \<and>
         valid_sops ts\<^sub>s\<^sub>b\<^sub>h' \<and> load_tmps_fresh ts\<^sub>s\<^sub>b\<^sub>h' \<and> enough_flushs ts\<^sub>s\<^sub>b\<^sub>h' \<and>
         valid_program_history ts\<^sub>s\<^sub>b\<^sub>h' \<and> valid ts\<^sub>s\<^sub>b\<^sub>h' \<and>
           (\<exists>ts' \<S>' m'. (ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>') \<and> 
            (ts\<^sub>s\<^sub>b\<^sub>h',m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b\<^sub>h') \<sim> (ts',m',\<S>'))"
proof -
  from concurrent_history_steps_simulates_store_buffer_step [OF step_sb sim_h]
  obtain ts\<^sub>s\<^sub>b\<^sub>h' \<S>\<^sub>s\<^sub>b\<^sub>h' where
    steps_h: "(ts\<^sub>s\<^sub>b\<^sub>h,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b\<^sub>h) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>s\<^sub>b\<^sub>h',m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b\<^sub>h')" and
    sim_h': "ts\<^sub>s\<^sub>b' \<sim>\<^sub>h ts\<^sub>s\<^sub>b\<^sub>h'"
    by blast
  moreover
  from concurrent_direct_steps_simulates_store_buffer_history_steps [OF steps_h
  valid_own valid_sb_reads valid_hist valid_sharing tmps_distinct valid_sops valid_dd
  load_tmps_fresh enough_flushs valid_program_history valid sim safe_reach]
  obtain m' ts' \<S>' where
    "(ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>')" "(ts\<^sub>s\<^sub>b\<^sub>h', m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b\<^sub>h') \<sim> (ts', m', \<S>')"
    "valid_ownership \<S>\<^sub>s\<^sub>b\<^sub>h' ts\<^sub>s\<^sub>b\<^sub>h'" "valid_reads m\<^sub>s\<^sub>b' ts\<^sub>s\<^sub>b\<^sub>h'" "valid_history program_step ts\<^sub>s\<^sub>b\<^sub>h'"
    "valid_sharing \<S>\<^sub>s\<^sub>b\<^sub>h' ts\<^sub>s\<^sub>b\<^sub>h'" "tmps_distinct ts\<^sub>s\<^sub>b\<^sub>h'" "valid_data_dependency ts\<^sub>s\<^sub>b\<^sub>h'"
    "valid_sops ts\<^sub>s\<^sub>b\<^sub>h'" "load_tmps_fresh ts\<^sub>s\<^sub>b\<^sub>h'" "enough_flushs ts\<^sub>s\<^sub>b\<^sub>h'"
    "valid_program_history ts\<^sub>s\<^sub>b\<^sub>h'" "valid ts\<^sub>s\<^sub>b\<^sub>h'"
    by blast
  ultimately
  show ?thesis
    by blast
qed

(* ******************* Some tuned version for presentations ********************************** *)

lemma conj_commI: "P \<and> Q \<Longrightarrow> Q \<and> P"
  by simp
lemma def_to_eq: "P = Q \<Longrightarrow> P \<equiv> Q"
  by simp

context xvalid_program
begin

definition 
"invariant ts \<S> m \<equiv> 
  valid_ownership \<S> ts \<and> valid_reads m ts \<and> valid_history program_step ts \<and> 
  valid_sharing \<S> ts \<and> tmps_distinct ts \<and> valid_data_dependency ts \<and> 
  valid_sops ts \<and>  load_tmps_fresh ts \<and> enough_flushs ts \<and> valid_program_history ts \<and> 
  valid ts"

definition "ownership_inv \<equiv> valid_ownership" 
definition "sharing_inv \<equiv>  valid_sharing"
definition "temporaries_inv ts \<equiv> tmps_distinct ts \<and> load_tmps_fresh ts"
definition "history_inv ts m \<equiv> valid_history program_step ts \<and> valid_program_history ts \<and> valid_reads m ts"
definition "data_dependency_inv ts \<equiv> valid_data_dependency ts \<and> load_tmps_fresh ts \<and> valid_sops ts"
definition "barrier_inv \<equiv> enough_flushs" 

lemma invariant_grouped_def: "invariant ts \<S> m \<equiv>
 ownership_inv \<S> ts \<and> sharing_inv \<S> ts \<and> temporaries_inv ts \<and> data_dependency_inv ts \<and> history_inv ts m \<and> barrier_inv ts \<and> valid ts"
  apply (rule def_to_eq)
  apply (auto simp add: ownership_inv_def sharing_inv_def barrier_inv_def temporaries_inv_def history_inv_def data_dependency_inv_def invariant_def)
  done


theorem (in xvalid_program) simulation':
  assumes step_sb: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h (ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b')"
  assumes sim: "(ts\<^sub>s\<^sub>b,m\<^sub>s\<^sub>b,\<S>\<^sub>s\<^sub>b) \<sim> (ts,m,\<S>)"
  assumes inv: "invariant ts\<^sub>s\<^sub>b \<S>\<^sub>s\<^sub>b m\<^sub>s\<^sub>b"
  assumes safe_reach: "safe_reach_direct safe_delayed (ts,m,\<S>)"
  shows "invariant ts\<^sub>s\<^sub>b' \<S>\<^sub>s\<^sub>b' m\<^sub>s\<^sub>b' \<and>
           (\<exists>ts' \<S>' m'. (ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>') \<and> (ts\<^sub>s\<^sub>b',m\<^sub>s\<^sub>b',\<S>\<^sub>s\<^sub>b') \<sim> (ts',m',\<S>'))"
  using inv sim safe_reach
  apply (unfold invariant_def)
  apply (simp only: conj_assoc)
  apply (rule "concurrent_direct_steps_simulates_store_buffer_history_step" [OF step_sb])
  apply simp_all
  done

lemmas (in xvalid_program) simulation = conj_commI [OF simulation']
end

end
