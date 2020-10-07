(*  Title:      perfect/HMLSL_Perfect.thy
    Author:     Sven Linker

Defines HMLSL with perfect sensors for cars. Cars can perceive both
the physical size and braking distance of all other cars.
*)

section\<open>HMLSL for Perfect Sensors\<close>
text \<open>
Within this section, we instantiate HMLSL for cars with 
perfect sensors.
\<close>


theory HMLSL_Perfect
  imports "../HMLSL" "Perfect_Sensors"
begin
  
  
locale hmlsl_perfect = perfect_sensors + restriction
begin
  
interpretation hmlsl : hmlsl "perfect :: cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
proof unfold_locales 
  
  fix e ts c
  show " 0 < perfect e ts c" 
    by (metis less_add_same_cancel2 less_trans perfect_def traffic.psGeZero
        traffic.sdGeZero) 
qed
  
notation hmlsl.re ("re'(_')")
notation hmlsl.cl("cl'(_')")
notation hmlsl.len ("len")

text \<open>
 The spatial atoms are independent of the perspective of the view. 
Hence we can prove several lemmas on the relation between the hybrid modality
and the spatial atoms.
\<close>
  
lemma at_res1:"\<Turnstile>(re(c)) \<^bold>\<rightarrow> (\<^bold>\<forall>d. \<^bold>@d re(c))" 
  by (metis (no_types, lifting) perfect_sensors.switch_length_stable 
      restriction.switch_restrict_stable view.switch_def)
    
lemma at_res2:"\<Turnstile>(\<^bold>\<forall>d. \<^bold>@d re(c)) \<^bold>\<rightarrow> re(c)" 
  using view.switch_refl by blast
    
lemma at_res:"\<Turnstile>re(c) \<^bold>\<leftrightarrow> (\<^bold>\<forall>d. \<^bold>@d re(c))"
  using at_res1 at_res2 by blast
    
lemma at_res_inst:"\<Turnstile> (\<^bold>@d re(c)) \<^bold>\<rightarrow>re(c)"
proof (rule allI|rule impI)+
  fix ts v
  assume assm:"ts,v \<Turnstile>( \<^bold>@d re(c))"
  obtain v' where v'_def:"(v=(d)> v') "
    using view.switch_always_exists by blast
  with assm have v':"ts,v' \<Turnstile> re(c)" by blast
  with v' show "ts,v \<Turnstile>re(c)" 
    using restriction.switch_restrict_stable perfect_sensors.switch_length_stable v'_def
      view.switch_def 
    by (metis (no_types, lifting) all_own_ext_eq_len_eq)
qed
  
lemma at_clm1:"\<Turnstile>cl(c) \<^bold>\<rightarrow> (\<^bold>\<forall>d. \<^bold>@d cl(c))"
  by (metis (no_types, lifting)  all_own_ext_eq_len_eq view.switch_def 
      restriction.switch_restrict_stable)
    
lemma at_clm2:"\<Turnstile>(\<^bold>\<forall>d. \<^bold>@d cl(c)) \<^bold>\<rightarrow> cl(c)" 
  using view.switch_def by auto
  
lemma at_clm:"\<Turnstile>cl(c) \<^bold>\<leftrightarrow> (\<^bold>\<forall>d. \<^bold>@d cl(c))"
  using at_clm1 at_clm2 by blast
    
lemma at_clm_inst:"\<Turnstile> (\<^bold>@d cl(c)) \<^bold>\<rightarrow>cl(c)" 
proof (rule allI|rule impI)+
  fix ts v
  assume assm:"ts,v \<Turnstile>( \<^bold>@d cl(c))"
  obtain v' where v'_def:"(v=(d)> v') "
    using view.switch_always_exists by blast
  with assm have v':"ts,v' \<Turnstile> cl(c)" by blast
  with v' show "ts,v \<Turnstile>cl(c)"
    using restriction.switch_restrict_stable switch_length_stable v'_def view.switch_def 
    by (metis (no_types, lifting) all_own_ext_eq_len_eq)
qed

text\<open>
With the definition of sensors, we can also express how the spatial situation
changes after the different transitions. In particular, we can prove 
lemmas corresponding to the activity and stability rules of the
proof system for MLSL \cite{Linker2015a}.

Observe that we were not able to prove these rules for basic HMLSL, since 
its generic sensor function allows for instantiations where the perceived length changes
during spatial transitions.
\<close>
  
lemma backwards_res_act:
  "(ts \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c) \<^bold>\<or> cl(c))" 
proof
  assume assm:"(ts \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c))"
  from assm have len_eq:"len v ts c = len v ts' c"
    using create_reservation_length_stable by blast
  have "res ts c \<sqsubseteq> res ts' c" using assm traffic.create_res_subseteq1 by blast
  hence restr_subs_res:"restrict v (res ts) c \<sqsubseteq> restrict v (res ts') c"
    by (simp add: restriction.restrict_view assm)
  have "clm ts c \<sqsubseteq> res ts' c" using assm traffic.create_res_subseteq2 by blast
  hence restr_subs_clm:"restrict v (clm ts) c \<sqsubseteq> restrict v (res ts') c"
    by (simp add: restriction.restrict_view assm)
  have "restrict v (res ts) c = \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>" by simp
  then show " ts,v \<Turnstile> (re(c) \<^bold>\<or> cl(c))" 
  proof
    assume restr_res_nonempty:"restrict v (res ts) c \<noteq> \<emptyset>"
    hence restrict_one:"|restrict v (res ts) c | = 1" 
      using nat_int.card_non_empty_geq_one nat_int.card_subset_le dual_order.antisym
        restr_subs_res assm by fastforce
    have "restrict v (res ts ) c \<sqsubseteq> lan v" 
      using restr_subs_res assm by auto
    hence "restrict v (res ts)c = lan v" 
      using restriction.restrict_eq_lan_subs restrict_one assm by auto
    thus " ts,v \<Turnstile> (re(c) \<^bold>\<or> cl(c))" 
      using assm len_eq by auto
  next
    assume restr_res_empty:"restrict v (res ts) c = \<emptyset>"
    then have clm_non_empty:" restrict v (clm ts) c \<noteq> \<emptyset>" 
      by (metis assm inter_empty2 local.hmlsl.free_no_clm 
          restriction.create_reservation_restrict_union restriction.restrict_def' 
          un_empty_absorb1)
    hence restrict_one:"|restrict v (clm ts) c | = 1" 
      using nat_int.card_non_empty_geq_one nat_int.card_subset_le dual_order.antisym
        restr_subs_clm assm by fastforce
    have "restrict v (clm ts ) c \<sqsubseteq> lan v" 
      using restr_subs_clm assm by auto
    hence "restrict v (clm ts)c = lan v"
      using restriction.restrict_eq_lan_subs restrict_one assm by auto
    thus " ts,v \<Turnstile> (re(c) \<^bold>\<or> cl(c))" 
      using assm len_eq by auto
  qed
qed
  
lemma backwards_res_act_somewhere:
  "(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> \<^bold>\<langle>re(c)\<^bold>\<rangle>) \<longrightarrow> (ts,v \<Turnstile>\<^bold>\<langle> re(c) \<^bold>\<or> cl(c)\<^bold>\<rangle> )"
  using backwards_res_act by blast 

lemma backwards_res_stab:
  "(ts \<^bold>\<midarrow>r(d) \<^bold>\<rightarrow> ts') \<and>  (d \<noteq>c) \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))"
  using perfect_sensors.create_reservation_length_stable restriction.restrict_def'
    traffic.create_res_subseteq1_neq 
  by auto
  
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
  by (metis inf.absorb1 order_trans perfect_sensors.withdraw_reservation_length_stable
      restriction.restrict_def' restriction.restrict_res traffic.withdraw_res_subseteq)

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
    show ?thesis 
      by (metis inf.absorb1 order_trans perfect_sensors.create_reservation_length_stable
          re restriction.restrict_def' restriction.restrict_subseteq 
          traffic.create_res_subseteq1 ts'_def)
  next
    assume cl:"ts,v \<Turnstile>cl(c)"
    show ?thesis 
      by (metis cl inf.absorb1 order_trans perfect_sensors.create_reservation_length_stable
          restriction.restrict_def' restriction.restrict_subseteq
          traffic.create_res_subseteq2 ts'_def)
  qed
qed
  
lemma reservation2: "\<Turnstile>(\<^bold>\<box>r(c) re(c)) \<^bold>\<rightarrow> (re(c) \<^bold>\<or> cl(c))" 
  using backwards_res_act traffic.always_create_res by blast
    
lemma reservation:"\<Turnstile>(\<^bold>\<box>r(c) re(c)) \<^bold>\<leftrightarrow> (re(c) \<^bold>\<or> cl(c))"
  using reservation1 reservation2 by blast
end
end
  
