subsection\<open>SC and Implication-only formulas\<close>
theory MiniSC
imports MiniFormulas SC
begin

abbreviation "is_mini_mset \<Gamma> \<equiv> \<forall>F \<in> set_mset \<Gamma>. is_mini_formula F"
lemma to_mini_mset_is: "is_mini_mset (image_mset to_mini_formula \<Gamma>)" by simp

lemma SC_full_to_mini:
  defines "tms \<equiv> image_mset to_mini_formula"
  assumes asm: "\<Gamma> \<Rightarrow> \<Delta>"
  shows "tms \<Gamma> \<Rightarrow> tms \<Delta>"
proof -
  have tmsi[simp]: "tms (F,S) = to_mini_formula F, tms S" for F S unfolding tms_def by simp
  from asm show ?thesis
  proof(induction \<Gamma> \<Delta> rule: SCp.induct)
    case (BotL \<Gamma>)
    hence "\<bottom> \<in># tms \<Gamma>" unfolding tms_def by force
    thus ?case using SCp.BotL by blast
  next
    case (Ax k \<Gamma> \<Delta>)
    hence "Atom k \<in># tms \<Gamma>" "Atom k \<in># tms \<Delta>" unfolding tms_def using image_iff by fastforce+
    thus ?case using SCp.Ax[of k] by blast
  next
    case (NotR F \<Gamma> \<Delta>) thus ?case 
      unfolding tmsi to_mini_formula.simps
      using weakenR SCp.ImpR by blast
  next
    case (NotL \<Gamma> F \<Delta>) from this(2) show ?case
      by(auto intro!: SCp.ImpL)
  next
    case ImpR thus ?case using SCp.ImpR by simp
  next
    case ImpL thus ?case using SCp.ImpL by simp
  next
    case AndR from AndR(3,4) show ?case 
      using weakenR by(auto intro!: SCp.ImpR SCp.ImpL)
  next
    case AndL from AndL(2) show ?case 
      using weakenR[where 'a='a] by(fastforce intro!: SCp.ImpR SCp.ImpL)
  next
    case OrR from OrR(2) show ?case
      using weakenR by(fastforce intro!: SCp.ImpR SCp.ImpL)
  next
    case (OrL F \<Gamma> \<Delta> G)
    note SCp.ImpL
    moreover {
      have "to_mini_formula F, tms \<Gamma> \<Rightarrow> tms \<Delta>" using  OrL(3)[unfolded tmsi] .
      with weakenR have "to_mini_formula F, tms \<Gamma> \<Rightarrow> \<bottom>, tms \<Delta>" by blast (* sooo close. *)
      with SCp.ImpR have "tms \<Gamma> \<Rightarrow> to_mini_formula F \<^bold>\<rightarrow> \<bottom>, tms \<Delta>" . }
    moreover have "to_mini_formula G, tms \<Gamma> \<Rightarrow> tms \<Delta>" using \<open>tms (G, \<Gamma>) \<Rightarrow> tms \<Delta>\<close> unfolding tmsi .
    ultimately have "(to_mini_formula F \<^bold>\<rightarrow> \<bottom>) \<^bold>\<rightarrow> to_mini_formula G, tms \<Gamma> \<Rightarrow> tms \<Delta>" .
    thus ?case unfolding tmsi to_mini_formula.simps .
  qed
qed
  
lemma SC_mini_to_full:
  defines "tms \<equiv> image_mset to_mini_formula"
  assumes asm: "tms \<Gamma> \<Rightarrow> tms \<Delta>"
  shows "\<Gamma> \<Rightarrow> \<Delta>"
proof -
  have tmsi[simp]: "tms (F,S) = to_mini_formula F, tms S" for F S unfolding tms_def by simp
  note ImpL_inv ImpR_inv[dest]
  have no: "f \<noteq> (\<lambda>F G. Not F)" "f \<noteq> Or" "f \<noteq> And" if "f F G, S' = tms S" for f F G S S'
    by (metis that is_mini_formula.simps(4-6) msed_map_invR tms_def to_mini_is_mini union_commute)+
  note dr = no(1)[where f="\<lambda>F G. Not F", simplified, dest!]
            no(2)[where f=Or, simplified, dest!] 
            no(3)[where f=And, simplified, dest!]
  have whai(* we have an implication *): "
    (\<exists>S2 H J. S = H \<^bold>\<rightarrow> J, S2 \<and> F = to_mini_formula H \<and> G = to_mini_formula J) \<or>
    (\<exists>S2 H J. S = H \<^bold>\<or> J, S2 \<and> F = (to_mini_formula H \<^bold>\<rightarrow> \<bottom>) \<and> G = to_mini_formula J) \<or>
    (\<exists>S2 H J. S = H \<^bold>\<and> J, S2 \<and> F =  to_mini_formula H \<^bold>\<rightarrow> to_mini_formula J \<^bold>\<rightarrow> \<bottom> \<and> G = \<bottom>) \<or>
    (\<exists>S2 H. S = \<^bold>\<not> H, S2 \<and> F = to_mini_formula H \<and> G = \<bottom>)
  " if "F \<^bold>\<rightarrow> G, S1 = tms S" for F G S1 S proof - (* ohno\<dots> *)
    note that[unfolded tms_def]
    then obtain S2 pim where S2: "S1 = image_mset to_mini_formula S2"
                        and   S: "S = pim, S2"
                        and pim: "F \<^bold>\<rightarrow> G = to_mini_formula pim"
      by (metis msed_map_invR union_commute)
    show ?thesis using pim unfolding S by(cases pim; simp; blast)
  qed
  from asm show ?thesis
  proof(induction "tms \<Gamma>"  "tms \<Delta>" arbitrary: \<Gamma> \<Delta> rule: SCp.induct)
    have *: "to_mini_formula F = \<bottom> \<Longrightarrow> F = \<bottom>" for F by(cases F; simp)
    case BotL thus ?case unfolding tms_def using * SCp.BotL by (metis image_iff multiset.set_map)
  next
    have *: "Atom k = to_mini_formula F \<Longrightarrow> F = Atom k" for F k by(cases F; simp)
    case (Ax _ k) thus ?case
      unfolding tms_def unfolding in_image_mset Set.image_iff
      apply(elim bexE)
      apply(drule *)+
      apply(intro SCp.Ax)
    by simp_all
  next
    case (ImpL \<Gamma>' F G)
    note whai[OF ImpL(5)]
    thus ?case proof(elim disjE exE conjE)
      fix S2 H J
      assume *: "\<Gamma> = H \<^bold>\<rightarrow> J, S2" "F = to_mini_formula H" "G = to_mini_formula J"
      hence "\<Gamma>' = tms S2" "F, tms \<Delta> = tms (H,\<Delta>)" "G, \<Gamma>' = tms (J, S2)" "tms \<Delta> = tms \<Delta>" using ImpL.hyps(5) add_left_imp_eq by auto
      from ImpL(2)[OF this(1,2)] ImpL(4)[OF this(3-)]
      show ?thesis using SCp.ImpL by(simp add: *)
    next
      fix S2 H J
      assume *: "\<Gamma> = H \<^bold>\<or> J, S2" "F = to_mini_formula H \<^bold>\<rightarrow> \<bottom>" "G = to_mini_formula J"
      hence "\<Gamma>' = tms S2" "F, tms \<Delta> = tms (H \<^bold>\<rightarrow> \<bottom>,\<Delta>)" "G, \<Gamma>' = tms (J, S2)" "tms \<Delta> = tms \<Delta>" using ImpL.hyps(5) add_left_imp_eq by auto
      from ImpL(2)[OF this(1,2)] ImpL(4)[OF this(3-)]
      show ?thesis using Bot_delR by(force intro!: SCp.OrL dest!: ImpR_inv simp: *)
    next
      fix S2 H J
      assume *: "\<Gamma> = H \<^bold>\<and> J, S2" "F = to_mini_formula H \<^bold>\<rightarrow> to_mini_formula J \<^bold>\<rightarrow> \<bottom>" "G = \<bottom>"
      hence "\<Gamma>' = tms S2" "F, tms \<Delta> = tms (H \<^bold>\<rightarrow> J \<^bold>\<rightarrow> \<bottom>,\<Delta>)" "G, \<Gamma>' = tms (\<bottom>, S2)" "tms \<Delta> = tms \<Delta>" using ImpL.hyps(5) add_left_imp_eq by auto
      from ImpL(2)[OF this(1,2)]
      show ?thesis using Bot_delR SCp.AndL ImpR_inv * by (metis add_mset_remove_trivial inL1)
    next
      fix S2 H
      assume *: "\<Gamma> = \<^bold>\<not> H, S2" "F = to_mini_formula H" "G = \<bottom>"
      hence "\<Gamma>' = tms S2" "F, tms \<Delta> = tms (H,\<Delta>)" "G, \<Gamma>' = tms (\<bottom>, S2)" "tms \<Delta> = tms \<Delta>" using ImpL.hyps(5) add_left_imp_eq by auto
      from ImpL(2)[OF this(1,2)]
      show ?thesis by(force intro!: SCp.NotL dest!: ImpR_inv simp: *)
    qed
  next
    case (ImpR F G \<Delta>')
    note whai[OF ImpR(3)]
    thus ?case proof(elim disjE  exE conjE)
      fix S2 H J
      assume "\<Delta> = H \<^bold>\<rightarrow> J, S2" "F = to_mini_formula H" "G = to_mini_formula J"
      thus ?thesis using ImpR.hyps(2,3) by (auto intro!: SCp.ImpR)
    next
      fix S2 H J
      assume *: "\<Delta> = H \<^bold>\<or> J, S2" "F = to_mini_formula H \<^bold>\<rightarrow> \<bottom>" "G = to_mini_formula J"
      hence "\<Delta>' = tms S2" "F, tms \<Delta> = tms (H \<^bold>\<rightarrow> \<bottom>,\<Delta>)" "G, \<Delta>' = tms (J, S2)" "tms \<Delta> = tms \<Delta>" using ImpR.hyps(3) add_left_imp_eq by auto
      thus ?thesis using SCp.OrR[where 'a='a] * ImpR.hyps(2) by (simp add: NotL_inv)
    next
      have botoff: "\<Gamma> \<Rightarrow> H, \<bottom>, S2 \<Longrightarrow> \<Gamma> \<Rightarrow> H, S2" for \<Gamma> H S2 using Bot_delR by fastforce
      fix S2 H J
      assume *: "\<Delta> = H \<^bold>\<and> J, S2" "F = to_mini_formula H \<^bold>\<rightarrow> to_mini_formula J \<^bold>\<rightarrow> \<bottom>" "G = \<bottom>"
      hence "F, tms \<Gamma> = tms (H \<^bold>\<rightarrow> J \<^bold>\<rightarrow> \<bottom>, \<Gamma>)" " G, \<Delta>' = tms (\<bottom>, S2)"
        using ImpR.hyps(3) by(auto) (* hm, not optimal that we need mini_mini\<dots> *)
      from ImpR(2)[OF this] show ?thesis by(auto simp add: * intro!: SCp.intros(3-) dest!: ImpL_inv botoff)
    next  
      (* verbose version *)
      fix S2 H
      assume "\<Delta> = \<^bold>\<not> H, S2" "F = to_mini_formula H" "G = \<bottom>"
      then obtain S2 H where *: "\<Delta> = \<^bold>\<not> H, S2" "F = to_mini_formula H \<and> G = \<bottom>" by blast
      hence "F, tms \<Gamma> = tms (H, \<Gamma>)" "G, \<Delta>' = tms (\<bottom>, S2)" using ImpR(3) by simp_all
      with ImpR(2) have "H, \<Gamma> \<Rightarrow> \<bottom>, S2" .
      hence "\<Gamma> \<Rightarrow> \<^bold>\<not> H, S2" using SCp.NotR Bot_delR by fastforce
      thus "\<Gamma> \<Rightarrow> \<Delta>" by(simp add: *)
    qed
  qed auto
qed

theorem MiniSC_eq: "image_mset to_mini_formula \<Gamma> \<Rightarrow> image_mset to_mini_formula \<Delta> \<longleftrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
  using SC_mini_to_full SC_full_to_mini by blast

end
