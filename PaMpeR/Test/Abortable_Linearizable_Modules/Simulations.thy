section {* Definition and Soundness of Refinement Mappings,
  Forward Simulations and Backward Simulations *}

theory Simulations
imports IOA
begin

context IOA
begin

definition refines where
  "refines e s a t A f \<equiv> fst e = f s \<and> last_state e = f t \<and> is_exec_frag_of A e
            \<and> (let tr = trace (ioa.asig A) e in 
                if a \<in> ext A then tr = [a] else tr = [])"
definition
  is_ref_map :: "('s1 \<Rightarrow> 's2) \<Rightarrow> ('s1,'a)ioa \<Rightarrow> ('s2,'a)ioa \<Rightarrow> bool" where
  "is_ref_map f B A \<equiv>
    (\<forall> s \<in> start B . f s \<in> start A) \<and> (\<forall> s t a. reachable B s \<and> s \<midarrow>a\<midarrow>B\<longrightarrow> t
      \<longrightarrow> (\<exists> e . refines e s a t A f ))"

definition
  is_forward_sim :: "('s1 \<Rightarrow> ('s2 set)) \<Rightarrow> ('s1,'a)ioa \<Rightarrow> ('s2,'a)ioa \<Rightarrow> bool" where
  "is_forward_sim f B A \<equiv>
   (\<forall> s \<in> start B . f s \<inter> start A \<noteq> {})
   \<and> (\<forall> s s' t a. s' \<in> f s \<and> s \<midarrow>a\<midarrow>B\<longrightarrow> t \<and> reachable B s
        \<longrightarrow> (\<exists> e . fst e = s' \<and> last_state e \<in> f t \<and> is_exec_frag_of A e
              \<and> (let tr = trace (ioa.asig A) e in 
                    if a \<in> ext A then tr = [a] else tr = [])))"

definition
  is_backward_sim :: "('s1 \<Rightarrow> ('s2 set)) \<Rightarrow> ('s1,'a)ioa \<Rightarrow> ('s2,'a)ioa \<Rightarrow> bool" where
  "is_backward_sim f B A \<equiv>
   (\<forall> s . f s \<noteq> {}) (* Quantifying over reachable states would suffice *)
   \<and> (\<forall> s \<in> start B . f s \<subseteq> start A)
   \<and> (\<forall> s t a t'. t' \<in> f t \<and> s \<midarrow>a\<midarrow>B\<longrightarrow> t \<and> reachable B s
        \<longrightarrow> (\<exists> e . fst e \<in> f s \<and> last_state e = t' \<and> is_exec_frag_of A e
                \<and> (let tr = trace (ioa.asig A) e in 
                      if a \<in> ext A then tr = [a] else tr = [])))"

subsection {* A series of lemmas that will be useful in the soundness proofs *}

lemma step_eq_traces:
  fixes e_B' A e e_A' a t
  defines "e_A \<equiv> append_exec e_A' e" and "e_B \<equiv> cons_exec e_B' (a,t)"
  and "tr \<equiv> trace (ioa.asig A) e"
  assumes 1:"trace (ioa.asig A) e_A' = trace (ioa.asig A) e_B'"
  and 2:"if a \<in> ext A then tr = [a] else tr = []"
  shows "trace (ioa.asig A) e_A = trace (ioa.asig A) e_B"
proof -
  have 3:"trace (ioa.asig A) e_B = 
         (if a \<in> ext A then (trace (ioa.asig A) e_B') # a else trace (ioa.asig A) e_B')"
    using e_B_def by (simp add:trace_def schedule_def filter_act_def cons_exec_def)
  have 4:"trace (ioa.asig A) e_A = 
         (if a \<in> ext A then trace (ioa.asig A) e_A' # a else trace (ioa.asig A) e_A')"
    using 2 trace_append_is_append_trace[of "ioa.asig A" e_A' e] 
      by(auto simp add:e_A_def tr_def split: if_split_asm)
  show ?thesis using 1 3 4 by simp
qed

lemma exec_inc_imp_trace_inc:
  fixes A B
  assumes "ext B = ext A"
  and "\<And> e_B . is_exec_of B e_B 
    \<Longrightarrow> \<exists> e_A . is_exec_of A e_A \<and> trace (ioa.asig A) e_A = trace (ioa.asig A) e_B"
  shows "traces B \<subseteq> traces A"
proof -
  { fix t
    assume "t \<in> traces B"
    with this obtain e where 1:"t = trace (ioa.asig B) e" and 2:"is_exec_of B e"
      using traces_alt assms(1) by blast
    from 1 and assms(1) have 3:"t = trace (ioa.asig A) e" by (simp add:trace_def)
    from 2 3 and assms(2) obtain e' where 
      "is_exec_of A e' \<and> trace (ioa.asig A) e' = trace (ioa.asig A) e" by blast
    hence "t \<in> traces A" using 3 traces_alt by fastforce }
  thus ?thesis by fast
qed

subsection {* Soundness of Refinement Mappings *}

lemma ref_map_execs:
  fixes A::"('sA,'a)ioa" and B::"('sB,'a)ioa" and f::"'sB \<Rightarrow> 'sA" and e_B
  assumes "is_ref_map f B A" and "is_exec_of B e_B"
  shows "\<exists> e_A .  is_exec_of A e_A 
    \<and> trace (ioa.asig A) e_A = trace (ioa.asig A) e_B"
proof -
  note assms(2)
  hence "\<exists> e_A .  is_exec_of A e_A 
                  \<and> trace (ioa.asig A) e_A = trace (ioa.asig A) e_B 
                  \<and> last_state e_A = f (last_state e_B)"
  proof (induction "snd e_B" arbitrary:e_B)
    case Nil
    let ?e_A = "(f (fst e_B), [])"
    have "\<And> s . s \<in> start B \<Longrightarrow> f s \<in> start A" using assms(1) by (simp add:is_ref_map_def)
    hence "is_exec_of A ?e_A" using Nil.prems(1) by (simp add:is_exec_of_def)
    moreover
    have "trace (ioa.asig A) ?e_A = trace (ioa.asig A) e_B" 
      using Nil.hyps by (simp add:trace_simps)
    moreover
    have "last_state ?e_A = f (last_state e_B)" 
      using Nil.hyps by (metis last_state.simps(1) prod.collapse)
    ultimately show ?case by fast
  next
    case (Cons p ps e_B)
    let ?e_B' = "(fst e_B, ps)"
    let ?s = "last_state ?e_B'" let ?t = "snd p" let ?a = "fst p"
    have 1:"is_exec_of B ?e_B'" and 2:"?s\<midarrow>?a\<midarrow>B\<longrightarrow>?t"
      using Cons.prems and Cons.hyps(2)
        by (simp_all add:is_exec_of_def,
            cases "(B,fst e_B,ps#p)" rule:is_exec_frag_of.cases, auto,
            cases "(B,fst e_B,ps#p)" rule:is_exec_frag_of.cases, auto)
    with Cons.hyps(1) obtain e_A' where ih1:"is_exec_of A e_A'"
      and ih2:"trace (ioa.asig A) e_A' = trace (ioa.asig A) ?e_B'"
      and ih3:"last_state e_A' = f ?s" by fastforce
    from 1 have 3:"reachable B ?s" using last_state_reachable by fast
    obtain e where 4:"fst e = f ?s" and 5:"last_state e = f ?t" 
    and 6:"is_exec_frag_of A e"
    and 7:"let tr = trace (ioa.asig A) e in if ?a \<in> ext A 
      then tr = [?a] else tr = []" 
        using 2 and 3 and assms(1) 
          by (force simp add:is_ref_map_def refines_def)
    let ?e_A = "append_exec e_A' e"
    have "is_exec_of A ?e_A" 
      using ih1 ih3 4 6 append_exec_frags_is_exec_frag[of A e e_A']
        by (metis append_exec_def append_exec_frags_is_exec_frag 
          fst_conv is_exec_of_def) 
    moreover 
    have "trace (ioa.asig A) ?e_A = trace (ioa.asig A) e_B"
      using ih2 Cons.hyps(2) 7 step_eq_traces[of A e_A' ?e_B' ?a e]
        by (auto simp add:cons_exec_def) (metis prod.collapse)
    moreover have "last_state ?e_A = f ?t" using ih3 4 5 last_state_of_append 
      by metis
    ultimately show ?case using Cons.hyps(2) 
      by (metis last_state.simps(2) surjective_pairing)
  qed
  thus ?thesis by blast
qed

theorem ref_map_soundness:
  fixes A::"('sA,'a)ioa" and B::"('sB,'a)ioa" and f::"'sB \<Rightarrow> 'sA"
  assumes "is_ref_map f B A" and "ext A = ext B"
  shows "traces B \<subseteq> traces A"
  using assms ref_map_execs exec_inc_imp_trace_inc by metis

subsection {* Soundness of Forward Simulations *}

lemma forward_sim_execs:
  fixes A::"('sA,'a)ioa" and B::"('sB,'a)ioa" and f::"'sB \<Rightarrow> 'sA set" and e_B
  assumes "is_forward_sim f B A" and "is_exec_of B e_B"
  shows "\<exists> e_A .  is_exec_of A e_A 
    \<and> trace (ioa.asig A) e_A = trace (ioa.asig A) e_B"
proof -
  note assms(2)
  hence "\<exists> e_A .  is_exec_of A e_A 
                  \<and> trace (ioa.asig A) e_A = trace (ioa.asig A) e_B 
                  \<and> last_state e_A \<in> f (last_state e_B)"
  proof (induction "snd e_B" arbitrary:e_B)
    case Nil
    have "\<And> s . s \<in> start B \<Longrightarrow> f s \<inter> start A \<noteq> {}" 
      using assms(1) by (simp add:is_forward_sim_def)
    with this obtain s' where 1:"s' \<in> f (fst e_B)" and 2:"s' \<in> start A" 
      by (metis Int_iff Nil.prems all_not_in_conv is_exec_of_def)
    let ?e_A = "(s', [])"
    have "is_exec_of A ?e_A" using 2 by (simp add:is_exec_of_def)
    moreover
    have "trace (ioa.asig A) ?e_A = trace (ioa.asig A) e_B" using Nil.hyps 
      by (simp add:trace_def schedule_def filter_act_def)
    moreover 
    have "last_state ?e_A \<in> f (last_state e_B)" 
      using Nil.hyps 1 by (metis last_state.simps(1) surjective_pairing)
    ultimately show ?case by fast
  next
    case (Cons p ps e_B)
    let ?e_B' = "(fst e_B, ps)"
    let ?s = "last_state ?e_B'" let ?t = "snd p" let ?a = "fst p"
    have 1:"is_exec_of B ?e_B'" and 2:"?s\<midarrow>?a\<midarrow>B\<longrightarrow>?t"
      using Cons.prems and Cons.hyps(2)
        by (simp_all add:is_exec_of_def,
            cases "(B,fst e_B,ps#p)" rule:is_exec_frag_of.cases, auto,
            cases "(B,fst e_B,ps#p)" rule:is_exec_frag_of.cases, auto)
    with Cons.hyps(1) obtain e_A' where ih1:"is_exec_of A e_A'"
      and ih2:"trace (ioa.asig A) e_A' = trace (ioa.asig A) ?e_B'"
      and ih3:"last_state e_A' \<in> f ?s" by fastforce
    from 1 have 3:"reachable B ?s" using last_state_reachable by fast
    obtain e where 4:"fst e = last_state e_A'" and 5:"last_state e \<in> f ?t" 
    and 6:"is_exec_frag_of A e"
    and 7:"let tr = trace (ioa.asig A) e in if ?a \<in> ext A then tr = [?a] else tr = []" 
      using 2 3 assms(1) ih3 by (simp add:is_forward_sim_def) 
        (metis prod.collapse prod.inject)
    let ?e_A = "append_exec e_A' e"
    have "is_exec_of A ?e_A" 
      using ih1 ih3 4 6 append_exec_frags_is_exec_frag[of A e e_A']
        by (metis append_exec_def append_exec_frags_is_exec_frag 
            fst_conv is_exec_of_def) 
    moreover 
    have "trace (ioa.asig A) ?e_A = trace (ioa.asig A) e_B"
      using ih2 Cons.hyps(2) 7 step_eq_traces[of A e_A' ?e_B' ?a e]
        by (auto simp add:cons_exec_def Let_def) (metis prod.collapse)
    moreover have "last_state ?e_A \<in> f ?t" using ih3 4 5 last_state_of_append 
      by metis
    ultimately show ?case using Cons.hyps(2) 
      by (metis last_state.simps(2) surjective_pairing)
  qed
  thus ?thesis by blast
qed

theorem forward_sim_soundness:
  fixes A::"('sA,'a)ioa" and B::"('sB,'a)ioa" and f::"'sB \<Rightarrow> 'sA set"
  assumes "is_forward_sim f B A" and "ext A = ext B"
  shows "traces B \<subseteq> traces A"
  using assms forward_sim_execs exec_inc_imp_trace_inc by metis

subsection {* Soundness of Backward Simulations *}

lemma backward_sim_execs:
  fixes A::"('sA,'a)ioa" and B::"('sB,'a)ioa" and f::"'sB \<Rightarrow> 'sA set" and e_B
  assumes "is_backward_sim f B A" and "is_exec_of B e_B"
  shows "\<exists> e_A .  is_exec_of A e_A 
    \<and> trace (ioa.asig A) e_A = trace (ioa.asig A) e_B"
proof -
  note assms(2)
  hence "\<forall> s \<in> f (last_state e_B). \<exists> e_A .
          is_exec_of A e_A 
          \<and> trace (ioa.asig A) e_A = trace (ioa.asig A) e_B 
          \<and> last_state e_A = s"
  proof (induction "snd e_B" arbitrary:e_B)
    case Nil
    { fix s' assume 1:"s' \<in> f(last_state e_B)"
      have 2:"\<And> s . s \<in> start B \<Longrightarrow> f s \<subseteq> start A " 
        using assms(1) by (simp add:is_backward_sim_def)
      from Nil 1 2 have 3:"s' \<in> start A" 
        by (metis (full_types) is_exec_of_def last_state.simps(1) set_mp surjective_pairing)
      let ?e_A = "(s', [])"
      have 4:"is_exec_of A ?e_A" using 3 by (simp add:is_exec_of_def)
      have 5:"trace (ioa.asig A) ?e_A = trace (ioa.asig A) e_B" using Nil.hyps 
        by (simp add:trace_def schedule_def filter_act_def)
      have 6:"last_state ?e_A \<in> f (last_state e_B)" 
        using Nil.hyps 1 by (metis last_state.simps(1)) 
      note 4 5 6 }
    thus ?case by fastforce
  next
    case (Cons p ps e_B)
    { fix t' assume 8:"t' \<in> f (last_state e_B)"
      let ?e_B' = "(fst e_B, ps)"
      let ?s = "last_state ?e_B'" let ?t = "snd p" let ?a = "fst p"
      have 5:"?t = last_state e_B" using Cons.hyps(2) 
        by (metis last_state.simps(2) prod.collapse)
      have 1:"is_exec_of B ?e_B'" and 2:"?s\<midarrow>?a\<midarrow>B\<longrightarrow>?t"
        using Cons.prems and Cons.hyps(2)
          by (simp_all add:is_exec_of_def,
              cases "(B,fst e_B, ps#p)" rule:is_exec_frag_of.cases, auto,
              cases "(B,fst e_B, ps#p)" rule:is_exec_frag_of.cases, auto)
      from 1 have 3:"reachable B ?s" using last_state_reachable by fast
      obtain e where 4:"fst e \<in> f ?s" and 5:"last_state e = t'" 
      and 6:"is_exec_frag_of A e"
      and 7:"let tr = trace (ioa.asig A) e in 
        if ?a \<in> ext A then tr = [?a] else tr = []" 
        using 2 assms(1) 8 5 3 by (auto simp add: is_backward_sim_def, metis)
      obtain e_A' where ih1:"is_exec_of A e_A'" 
        and ih2:"trace (ioa.asig A) e_A' = trace (ioa.asig A) ?e_B'" 
        and ih3:"last_state e_A' = fst e"
          using 1 4 Cons.hyps(1) by (metis snd_conv)
      let ?e_A = "append_exec e_A' e"
      have "is_exec_of A ?e_A" 
        using ih1 ih3 4 6 append_exec_frags_is_exec_frag[of A e e_A']
          by (metis append_exec_def append_exec_frags_is_exec_frag 
            fst_conv is_exec_of_def) 
      moreover 
      have "trace (ioa.asig A) ?e_A = trace (ioa.asig A) e_B"
        using ih2 Cons.hyps(2) 7 step_eq_traces[of A e_A' ?e_B' ?a e]
          by (auto simp add:cons_exec_def Let_def) (metis prod.collapse)
      moreover have "last_state ?e_A = t'" using ih3 5 last_state_of_append 
        by metis
      ultimately have "\<exists> e_A . is_exec_of A e_A 
        \<and> trace (ioa.asig A) e_A = trace (ioa.asig A) e_B
        \<and> last_state e_A = t'" by blast }
    thus ?case by blast
  qed
  moreover
  from assms(1) have total:"\<And> s . f s \<noteq> {}" by (simp add:is_backward_sim_def)
  ultimately show ?thesis by fast
qed

theorem backward_sim_soundness:
  fixes A::"('sA,'a)ioa" and B::"('sB,'a)ioa" and f::"'sB \<Rightarrow> 'sA set"
  assumes "is_backward_sim f B A" and "ext A = ext B"
  shows "traces B \<subseteq> traces A"
  using assms backward_sim_execs exec_inc_imp_trace_inc by metis

end 

end
