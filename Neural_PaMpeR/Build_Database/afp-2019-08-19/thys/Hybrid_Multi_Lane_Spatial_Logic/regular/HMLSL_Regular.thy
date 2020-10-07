(*  Title:      regular/HMLSL_Regular.thy
    Author:     Sven Linker

Defines HMLSL with regular sensors for cars.
*)
section\<open>HMLSL for Regular Sensors\<close>
text \<open>
Within this section, we instantiate HMLSL for cars with 
regular sensors.
\<close>


theory HMLSL_Regular
  imports "../HMLSL" Regular_Sensors
begin
  
locale hmlsl_regular = regular_sensors + restriction
begin
interpretation hmlsl : hmlsl "regular :: cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
proof unfold_locales   
  fix e ts c
  show " 0 < regular e ts c"  
    by (metis less_add_same_cancel2 less_trans regular_def
        traffic.psGeZero traffic.sdGeZero) 
qed
  
notation hmlsl.re ("re'(_')")
notation hmlsl.cl("cl'(_')")
notation hmlsl.len ("len")

text \<open>
The spatial atoms are dependent of the perspective of the view,
hence we cannot prove similar lemmas as for perfect sensors.

However, we can still prove 
lemmas corresponding to the activity and stability rules of the
proof system for MLSL \cite{Linker2015a}.

Similar to the situation with perfect sensors, needed to instantiate the 
sensor function, to ensure that the perceived length does not change
during spatial transitions.
\<close>
  
lemma backwards_res_act:
  "(ts \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c) \<^bold>\<or> cl(c))"
proof
  assume assm:"(ts \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c))"
  from assm have len_eq:"len v ts c = len v ts' c"
    using create_reservation_length_stable by blast
  have "res ts c \<sqsubseteq> res ts' c" using assm traffic.create_res_subseteq1
    by auto
  hence restr_subs_res:"restrict v (res ts) c \<sqsubseteq> restrict v (res ts') c"    
    using assm restriction.restrict_view by auto 
  have "clm ts c \<sqsubseteq> res ts' c" using assm traffic.create_res_subseteq2     
    using assm restriction.restrict_view  by auto 
  hence restr_subs_clm:"restrict v (clm ts) c \<sqsubseteq> restrict v (res ts') c"     
    using assm restriction.restrict_view by auto 
  have "restrict v (res ts) c = \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>" by simp
  then show " ts,v \<Turnstile> (re(c) \<^bold>\<or> cl(c))" 
  proof
    assume restr_res_nonempty:"restrict v (res ts) c \<noteq> \<emptyset>"
    hence restrict_one:"|restrict v (res ts) c | = 1" 
      using nat_int.card_non_empty_geq_one nat_int.card_subset_le dual_order.antisym
        restr_subs_res assm by fastforce
    have "restrict v (res ts ) c \<sqsubseteq> lan v" using restr_subs_res assm by auto
    hence "restrict v (res ts)c = lan v" using restriction.restrict_eq_lan_subs
        restrict_one assm  by auto
    then show ?thesis using assm len_eq by auto
  next
    assume restr_res_empty:"restrict v (res ts) c = \<emptyset>"
    then have  clm_non_empty: "restrict v (clm ts) c \<noteq> \<emptyset>" 
      by (metis assm bot.extremum inf.absorb1 inf_commute local.hmlsl.free_no_clm
          restriction.create_reservation_restrict_union restriction.restrict_def
          un_empty_absorb1)
    then  have restrict_one:"|restrict v (clm ts) c | = 1" 
      using nat_int.card_non_empty_geq_one nat_int.card_subset_le dual_order.antisym
        restr_subs_clm assm by fastforce
    have "restrict v (clm ts ) c \<sqsubseteq> lan v" using restr_subs_clm assm by auto
    hence "restrict v (clm ts)c = lan v" using restriction.restrict_eq_lan_subs
        restrict_one assm   by auto
    then show ?thesis using assm len_eq by auto
  qed
qed

lemma backwards_res_act_somewhere:
  "(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> \<^bold>\<langle>re(c)\<^bold>\<rangle>) \<longrightarrow> (ts,v \<Turnstile>\<^bold>\<langle> re(c) \<^bold>\<or> cl(c)\<^bold>\<rangle> )"
  using backwards_res_act by blast 


lemma backwards_res_stab:
  "(ts \<^bold>\<midarrow>r(d) \<^bold>\<rightarrow> ts') \<and>  (d \<noteq>c) \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))" 
  using regular_sensors.create_reservation_length_stable restrict_def'
    traffic.create_res_subseteq1_neq by auto
  
lemma backwards_c_res_stab:
  "(ts \<^bold>\<midarrow>c(d,n) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))"
  using create_claim_length_stable traffic.create_clm_eq_res  
  by (metis (mono_tags, lifting) traffic.create_claim_def) 
    
lemma backwards_wdc_res_stab:
  "(ts \<^bold>\<midarrow>wdc(d) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))"
  using withdraw_claim_length_stable traffic.withdraw_clm_eq_res
  by (metis (mono_tags, lifting) traffic.withdraw_claim_def)
    
lemma backwards_wdr_res_stab:
  "(ts \<^bold>\<midarrow>wdr(d,n) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))" 
  by (metis inf.absorb1 order_trans regular_sensors.withdraw_reservation_length_stable
      restrict_def' restriction.restrict_res traffic.withdraw_res_subseteq)

text\<open>
We now proceed to prove the \emph{reservation lemma}, which was 
crucial in the manual safety proof \cite {Hilscher2011}. 
\<close>
lemma reservation1: "\<Turnstile>(re(c) \<^bold>\<or> cl(c)) \<^bold>\<rightarrow> \<^bold>\<box>r(c) re(c)"
proof (rule allI| rule impI)+ 
  fix ts v ts'
  assume assm:"ts,v \<Turnstile>re(c) \<^bold>\<or> cl(c)" and ts'_def:"ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow>ts'"
  from assm show "ts',v \<Turnstile>  re(c)" 
  proof
    assume re:"ts,v \<Turnstile>re(c)"
    then show ?thesis 
      by (metis inf.absorb1 order_trans regular_sensors.create_reservation_length_stable
          restrict_def' restriction.restrict_subseteq traffic.create_res_subseteq1 ts'_def)
  next
    assume cl:"ts,v \<Turnstile>cl(c)"
    then show ?thesis 
      by (metis inf.absorb1 order_trans regular_sensors.create_reservation_length_stable
          restrict_def' restriction.restrict_subseteq traffic.create_res_subseteq2 ts'_def)
  qed
qed

lemma reservation2: "\<Turnstile>(\<^bold>\<box>r(c) re(c)) \<^bold>\<rightarrow> (re(c) \<^bold>\<or> cl(c))" 
  using backwards_res_act traffic.always_create_res     
  by metis
    
lemma reservation:"\<Turnstile>(\<^bold>\<box>r(c) re(c)) \<^bold>\<leftrightarrow> (re(c) \<^bold>\<or> cl(c))"
  using reservation1 reservation2 by blast        
end
end
  
