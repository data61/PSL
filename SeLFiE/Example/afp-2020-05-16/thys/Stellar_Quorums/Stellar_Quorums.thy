text 
\<open>This theory formalizes some of the results appearing in the paper "Stellar Consensus By Reduction"\cite{disc_paper}.
We prove static properties of personal Byzantine quorum systems and Stellar quorum systems.\<close>

theory Stellar_Quorums
  imports Main 
begin

section "Personal Byzantine quorum systems"

locale personal_quorums =
  fixes quorum_of :: "'node \<Rightarrow> 'node set \<Rightarrow> bool" 
  assumes quorum_assm:"\<And> p p' . \<lbrakk>quorum_of p Q; p' \<in> Q\<rbrakk> \<Longrightarrow> quorum_of p' Q"
    \<comment> \<open>In other words, a quorum (of some participant) is a quorum of all its members.\<close>
begin

definition blocks where
  \<comment> \<open>Set @{term R} blocks participant @{term p}.\<close>
  "blocks R p \<equiv> \<forall> Q . quorum_of p Q \<longrightarrow> Q \<inter> R \<noteq> {}"

abbreviation blocked_by where "blocked_by R \<equiv> {p . blocks R p}"

lemma blocked_blocked_subset_blocked:
  "blocked_by (blocked_by R) \<subseteq> blocked_by R"
proof -
  have False if "p \<in> blocked_by (blocked_by R)" and "p \<notin> blocked_by R" for p
  proof -
    have "Q \<inter> blocked_by R \<noteq> {}" if "quorum_of p Q" for Q
      using \<open>p \<in> blocked_by (blocked_by R)\<close> that unfolding blocks_def by auto
    have "Q \<inter> R \<noteq> {}" if " quorum_of p Q" for Q
    proof -
      obtain p' where "p' \<in> blocked_by R" and "p' \<in> Q"
        by (meson Int_emptyI \<open>\<And>Q. quorum_of p Q \<Longrightarrow> Q \<inter> blocked_by R \<noteq> {}\<close> \<open>quorum_of p Q\<close>)
      hence "quorum_of p' Q"
        using quorum_assm that by blast
      with \<open>p' \<in> blocked_by R\<close> show "Q \<inter> R \<noteq> {}"
        using blocks_def by auto
    qed
    hence "p \<in> blocked_by R" by (simp add: blocks_def)
    thus False using that(2) by auto
  qed
  thus "blocked_by (blocked_by R) \<subseteq> blocked_by R"
    by blast
qed

end

text \<open>We now add the set of correct participants to the model.\<close>

locale with_w = personal_quorums quorum_of for quorum_of  :: "'node \<Rightarrow> 'node set \<Rightarrow> bool" +
  fixes W::"'node set" \<comment> \<open>@{term W} is the set of correct participants\<close>
begin

abbreviation B where "B \<equiv> -W"
  \<comment> \<open>@{term B} is the set of malicious participants.\<close>

definition quorum_of_set where "quorum_of_set S Q \<equiv> \<exists> p \<in> S . quorum_of p Q"

subsection "The set of participants not blocked by malicious participants"

definition L where "L \<equiv> W - (blocked_by B)"

lemma l2: "p \<in> L \<Longrightarrow> \<exists> Q  \<subseteq> W. quorum_of p Q" 
  unfolding L_def blocks_def using DiffD2 by auto
 
lemma l3: \<comment>  \<open>If a participant is not blocked by the malicious participants, then it has a quorum consisting exclusively of correct 
participants which are not blocked by the malicious participants.\<close>
  assumes "p \<in> L" shows "\<exists> Q \<subseteq> L . quorum_of p Q"
proof -
  have False if "\<And> Q . quorum_of p Q \<Longrightarrow> Q \<inter> (-L) \<noteq> {}"
  proof -
    obtain Q where "quorum_of p Q" and "Q \<subseteq> W" 
      using l2 \<open>p \<in> L\<close> by auto 
    have "Q \<inter> (-L) \<noteq> {}"  using that \<open>quorum_of p Q\<close> by simp
    obtain p' where "p' \<in> Q \<inter> (-L)" and "quorum_of p' Q"
      using \<open>Q \<inter> - L \<noteq> {}\<close> \<open>quorum_of p Q\<close> inf.left_idem quorum_assm by fastforce 
    hence "Q \<inter> B \<noteq> {}" unfolding L_def
      using CollectD Compl_Diff_eq Int_iff inf_le1 personal_quorums.blocks_def personal_quorums_axioms subset_empty by fastforce
    thus False using \<open>Q \<subseteq> W\<close> by auto  
  qed 
  thus ?thesis by (metis disjoint_eq_subset_Compl double_complement)
qed

subsection "Consensus clusters and intact sets"

definition is_intertwined where
  \<comment> \<open>This definition is not used in this theory,
    but we include it to formalize the notion of intertwined set appearing in the DISC paper.\<close>
  "is_intertwined S \<equiv> S \<subseteq> W 
    \<and> (\<forall> Q Q' . quorum_of_set S Q \<and> quorum_of_set S Q' \<longrightarrow> W \<inter> Q \<inter> Q' \<noteq> {})"

definition is_cons_cluster where
  \<comment> \<open>Consensus clusters\<close>
  "is_cons_cluster C \<equiv> C \<subseteq> W \<and> (\<forall> p \<in> C . \<exists> Q \<subseteq> C . quorum_of p Q)
      \<and> (\<forall> Q Q' . quorum_of_set C Q \<and> quorum_of_set C Q' \<longrightarrow> W \<inter> Q \<inter> Q' \<noteq> {})"

definition strong_consensus_cluster where
  "strong_consensus_cluster I \<equiv> I \<subseteq> W \<and> (\<forall> p \<in> I . \<exists> Q \<subseteq> I . quorum_of p Q)
      \<and> (\<forall> Q Q' . quorum_of_set I Q \<and> quorum_of_set I Q' \<longrightarrow> I \<inter> Q \<inter> Q' \<noteq> {})"

lemma strong_consensus_cluster_imp_cons_cluster:
\<comment> \<open>Every intact set is a consensus cluster\<close>
  shows "strong_consensus_cluster I \<Longrightarrow> is_cons_cluster I" 
  unfolding strong_consensus_cluster_def is_cons_cluster_def
  by blast 

lemma cons_cluster_neq_cons_cluster:
  \<comment> \<open>Some consensus clusters are not strong consensus clusters and have no superset that is a strong consensus cluster.\<close>
  shows "is_cons_cluster I \<and> (\<forall> J . I \<subseteq> J \<longrightarrow> \<not>strong_consensus_cluster J)" nitpick[falsify=false, card 'node=3, expect=genuine]
  oops

text \<open>Next we show that the union of two consensus clusters that intersect is a consensus cluster.\<close>

theorem cluster_union:
  assumes "is_cons_cluster C\<^sub>1" and "is_cons_cluster C\<^sub>2" and "C\<^sub>1 \<inter> C\<^sub>2 \<noteq> {}"
  shows "is_cons_cluster (C\<^sub>1\<union> C\<^sub>2)"
proof -
  have "C\<^sub>1 \<union> C\<^sub>2 \<subseteq> W"
    using assms(1) assms(2) is_cons_cluster_def by auto 
  moreover
  have "\<forall> p \<in> (C\<^sub>1\<union>C\<^sub>2) . \<exists> Q \<subseteq> (C\<^sub>1\<union>C\<^sub>2) . quorum_of p Q" 
    using \<open>is_cons_cluster C\<^sub>1\<close> \<open>is_cons_cluster C\<^sub>2\<close> unfolding is_cons_cluster_def
    by (meson UnE le_supI1 le_supI2)
  moreover
  have "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}"
    if "quorum_of_set (C\<^sub>1\<union>C\<^sub>2) Q\<^sub>1" and "quorum_of_set (C\<^sub>1\<union>C\<^sub>2) Q\<^sub>2" 
    for Q\<^sub>1 Q\<^sub>2
  proof -
    have "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" if "quorum_of_set C Q\<^sub>1" and "quorum_of_set C Q\<^sub>2" and "C = C\<^sub>1 \<or> C = C\<^sub>2" for C
      using \<open>is_cons_cluster C\<^sub>1\<close> \<open>is_cons_cluster C\<^sub>2\<close> \<open>quorum_of_set (C\<^sub>1\<union>C\<^sub>2) Q\<^sub>1\<close> \<open>quorum_of_set (C\<^sub>1\<union>C\<^sub>2) Q\<^sub>2\<close> that
      unfolding quorum_of_set_def is_cons_cluster_def by metis
    moreover
    have \<open>W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}\<close>  if "is_cons_cluster C\<^sub>1" and "is_cons_cluster C\<^sub>2"
      and "C\<^sub>1 \<inter> C\<^sub>2 \<noteq> {}" and "quorum_of_set C\<^sub>1 Q\<^sub>1" and "quorum_of_set C\<^sub>2 Q\<^sub>2"
    for C\<^sub>1 C\<^sub>2 \<comment> \<open>We generalize to avoid repeating the argument twice\<close>
    proof -
      obtain p Q where "quorum_of p Q" and "p \<in> C\<^sub>1 \<inter> C\<^sub>2" and "Q \<subseteq> C\<^sub>2" 
        using \<open>C\<^sub>1 \<inter> C\<^sub>2 \<noteq> {}\<close> \<open>is_cons_cluster C\<^sub>2\<close> unfolding is_cons_cluster_def by blast
      have "Q \<inter> Q\<^sub>1 \<noteq> {}" using \<open>is_cons_cluster C\<^sub>1\<close> \<open>quorum_of_set C\<^sub>1 Q\<^sub>1\<close> \<open>quorum_of p Q\<close> \<open>p \<in> C\<^sub>1 \<inter> C\<^sub>2\<close>
        unfolding is_cons_cluster_def quorum_of_set_def
        by (metis Int_assoc Int_iff inf_bot_right)
      hence "quorum_of_set C\<^sub>2 Q\<^sub>1"  using \<open>Q \<subseteq> C\<^sub>2\<close> \<open>quorum_of_set C\<^sub>1 Q\<^sub>1\<close> quorum_assm unfolding quorum_of_set_def by blast 
      thus "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" using \<open>is_cons_cluster C\<^sub>2\<close> \<open>quorum_of_set C\<^sub>2 Q\<^sub>2\<close>
        unfolding is_cons_cluster_def by blast
    qed
    ultimately show ?thesis using assms that unfolding quorum_of_set_def by auto 
  qed
  ultimately show ?thesis using assms
    unfolding is_cons_cluster_def by simp
qed

text \<open>Similarly, the union of two strong consensus clusters is a strong consensus cluster.\<close>
lemma strong_cluster_union:
  assumes "strong_consensus_cluster C\<^sub>1" and "strong_consensus_cluster C\<^sub>2" and "C\<^sub>1 \<inter> C\<^sub>2 \<noteq> {}"
  shows "strong_consensus_cluster (C\<^sub>1\<union> C\<^sub>2)"
proof -
  have "C\<^sub>1 \<union> C\<^sub>2 \<subseteq> W"
    using assms(1) assms(2) strong_consensus_cluster_def by auto 
  moreover
  have "\<forall> p \<in> (C\<^sub>1\<union>C\<^sub>2) . \<exists> Q \<subseteq> (C\<^sub>1\<union>C\<^sub>2) . quorum_of p Q" 
    using \<open>strong_consensus_cluster C\<^sub>1\<close> \<open>strong_consensus_cluster C\<^sub>2\<close> unfolding strong_consensus_cluster_def
    by (meson UnE le_supI1 le_supI2)
  moreover
  have "(C\<^sub>1\<union>C\<^sub>2) \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}"
    if "quorum_of_set (C\<^sub>1\<union>C\<^sub>2) Q\<^sub>1" and "quorum_of_set (C\<^sub>1\<union>C\<^sub>2) Q\<^sub>2" 
    for Q\<^sub>1 Q\<^sub>2
  proof -
    have "C \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" if "quorum_of_set C Q\<^sub>1" and "quorum_of_set C Q\<^sub>2" and "C = C\<^sub>1 \<or> C = C\<^sub>2" for C
      using \<open>strong_consensus_cluster C\<^sub>1\<close> \<open>strong_consensus_cluster C\<^sub>2\<close> that
      unfolding quorum_of_set_def strong_consensus_cluster_def by metis
    hence "(C\<^sub>1\<union>C\<^sub>2) \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" if "quorum_of_set C Q\<^sub>1" and "quorum_of_set C Q\<^sub>2" and "C = C\<^sub>1 \<or> C = C\<^sub>2" for C
      by (metis Int_Un_distrib2 disjoint_eq_subset_Compl sup.boundedE that)
    moreover
    have \<open>(C\<^sub>1\<union>C\<^sub>2) \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}\<close>  if "strong_consensus_cluster C\<^sub>1" and "strong_consensus_cluster C\<^sub>2"
      and "C\<^sub>1 \<inter> C\<^sub>2 \<noteq> {}" and "quorum_of_set C\<^sub>1 Q\<^sub>1" and "quorum_of_set C\<^sub>2 Q\<^sub>2"
    for C\<^sub>1 C\<^sub>2 \<comment> \<open>We generalize to avoid repeating the argument twice\<close>
    proof -
      obtain p Q where "quorum_of p Q" and "p \<in> C\<^sub>1 \<inter> C\<^sub>2" and "Q \<subseteq> C\<^sub>2" 
        using \<open>C\<^sub>1 \<inter> C\<^sub>2 \<noteq> {}\<close> \<open>strong_consensus_cluster C\<^sub>2\<close> unfolding strong_consensus_cluster_def by blast
      have "Q \<inter> Q\<^sub>1 \<noteq> {}" using \<open>strong_consensus_cluster C\<^sub>1\<close> \<open>quorum_of_set C\<^sub>1 Q\<^sub>1\<close> \<open>quorum_of p Q\<close> \<open>p \<in> C\<^sub>1 \<inter> C\<^sub>2\<close>
        unfolding strong_consensus_cluster_def quorum_of_set_def
        by (metis Int_assoc Int_iff inf_bot_right)
      hence "quorum_of_set C\<^sub>2 Q\<^sub>1"  using \<open>Q \<subseteq> C\<^sub>2\<close> \<open>quorum_of_set C\<^sub>1 Q\<^sub>1\<close> quorum_assm unfolding quorum_of_set_def by blast 
      thus "(C\<^sub>1\<union>C\<^sub>2) \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" using \<open>strong_consensus_cluster C\<^sub>2\<close> \<open>quorum_of_set C\<^sub>2 Q\<^sub>2\<close>
        unfolding strong_consensus_cluster_def by blast
    qed
    ultimately show ?thesis using assms that unfolding quorum_of_set_def by auto 
  qed
  ultimately show ?thesis using assms
    unfolding strong_consensus_cluster_def by simp
qed

end

section "Stellar quorum systems"

locale stellar =
  fixes slices :: "'node \<Rightarrow> 'node set set" \<comment> \<open>the quorum slices\<close>
    and W :: "'node set" \<comment> \<open>the well-behaved nodes\<close>
  assumes slices_ne:"\<And>p . p \<in> W \<Longrightarrow> slices p \<noteq> {}"
begin

definition quorum where
  "quorum Q \<equiv> \<forall> p \<in> Q \<inter> W . (\<exists> Sl \<in> slices p . Sl \<subseteq> Q)"

definition quorum_of where "quorum_of p Q \<equiv> quorum Q \<and> (p \<notin> W \<or> (\<exists> Sl \<in> slices p . Sl \<subseteq> Q))"
  \<comment> \<open>TODO: @{term "p\<notin>W"} needed?\<close>

lemma quorum_union:"quorum Q \<Longrightarrow> quorum Q' \<Longrightarrow> quorum (Q \<union> Q')"
  unfolding quorum_def
  by (metis IntE Int_iff UnE inf_sup_aci(1) sup.coboundedI1 sup.coboundedI2)

lemma l1:
  assumes "\<And> p . p \<in> S \<Longrightarrow> \<exists> Q \<subseteq> S . quorum_of p Q" and "p\<in> S"
  shows "quorum_of p S" using assms unfolding quorum_of_def quorum_def
  by (meson Int_iff subset_trans)

lemma is_pbqs:
  assumes "quorum_of p Q" and "p' \<in> Q"
  shows "quorum_of p' Q" 
  \<comment> \<open>This is the property required of a PBQS.\<close>
  using assms
  by (simp add: quorum_def quorum_of_def)

interpretation with_w quorum_of 
  \<comment> \<open>Stellar quorums form a personal quorum system.\<close>
  unfolding with_w_def personal_quorums_def 
  quorum_def quorum_of_def by simp

lemma quorum_is_quorum_of_some_slice:
  assumes "quorum_of p Q" and "p \<in> W"
  obtains S where "S \<in> slices p" and "S \<subseteq> Q"
    and "\<And> p' . p' \<in> S \<inter> W \<Longrightarrow> quorum_of p' Q"
  using assms unfolding quorum_def quorum_of_def by fastforce

lemma "is_cons_cluster C \<Longrightarrow> quorum C" 
  \<comment> \<open>Every consensus cluster is a quorum.\<close>
  unfolding is_cons_cluster_def
  by (metis inf.order_iff l1 quorum_of_def stellar.quorum_def stellar_axioms) 

subsection \<open>Properties of blocking sets\<close>

inductive blocking_min where
  \<comment> \<open>This is the set of correct participants that are eventually blocked by a set @{term R} when byzantine processors do not take steps.\<close>
  "\<lbrakk>p \<in> W; \<forall> Sl \<in> slices p . \<exists> q \<in> Sl\<inter>W . q \<in> R \<or> blocking_min R q\<rbrakk> \<Longrightarrow> blocking_min R p"
inductive_cases blocking_min_elim:"blocking_min R p"

inductive blocking_max where
  \<comment> \<open>This is the set of participants that are eventually blocked by a set @{term R} when byzantine processors help epidemic propagation.\<close>
  "\<lbrakk>p \<in> W; \<forall> Sl \<in> slices p . \<exists> q \<in> Sl . q \<in> R\<union>B \<or> blocking_max R q\<rbrakk> \<Longrightarrow> blocking_max R p"
inductive_cases "blocking_max R p"

text \<open>Next we show that if @{term \<open>R\<close>} blocks @{term \<open>p\<close>} and @{term p} belongs to a consensus cluster @{term S}, then @{term \<open>R \<inter> S \<noteq> {}\<close>}.\<close>

text \<open>We first prove two auxiliary lemmas:\<close>

lemma cons_cluster_wb:"p \<in> C \<Longrightarrow> is_cons_cluster C \<Longrightarrow> p\<in>W"
  using is_cons_cluster_def  by fastforce 

lemma cons_cluster_has_ne_slices:
  assumes "is_cons_cluster C" and "p\<in>C"
    and "Sl \<in> slices p" 
  shows "Sl \<noteq> {}"
  using assms unfolding is_cons_cluster_def quorum_of_set_def quorum_of_def quorum_def
  by (metis empty_iff inf_bot_left inf_bot_right subset_refl)

lemma cons_cluster_has_cons_cluster_slice:
  assumes "is_cons_cluster C" and "p\<in>C"
  obtains Sl where "Sl \<in> slices p" and "Sl \<subseteq> C"
  using assms unfolding is_cons_cluster_def quorum_of_set_def quorum_of_def quorum_def
  by (metis Int_commute  empty_iff inf.order_iff  inf_bot_right le_infI1)

theorem blocking_max_intersects_intact:
  \<comment> \<open>if @{term \<open>R\<close>} blocks @{term \<open>p\<close>} when malicious participants help epidemic propagation, 
and @{term p} belongs to a consensus cluster @{term C}, then @{term \<open>R \<inter> C \<noteq> {}\<close>}\<close>
  assumes  "blocking_max R p" and "is_cons_cluster C" and "p \<in> C"
  shows "R \<inter> C \<noteq> {}" using assms
proof (induct)
  case (1 p R)
  obtain Sl where "Sl \<in> slices p" and "Sl \<subseteq> C" using cons_cluster_has_cons_cluster_slice
    using "1.prems" by blast
  moreover have "Sl \<subseteq> W" using assms(2) calculation(2) is_cons_cluster_def by auto 
  ultimately show ?case
    using "1.hyps" assms(2) by fastforce
qed

text \<open>Now we show that if @{term \<open>p \<in> C\<close>}, @{term C} is a consensus cluster, and quorum @{term Q} is such that @{term \<open>Q \<inter> C \<noteq> {}\<close>},
    then @{term \<open>Q \<inter> W\<close>} blocks @{term p}. 

We start by defining the set of participants reachable from a participant through correct participants.
Their union trivially forms a quorum. 
Moreover, if @{term p} is not blocked by a set @{term R}, 
then we show that the set of participants reachable from @{term p} and not blocked by @{term R} forms a quorum disjoint from @{term R}.
It follows that if @{term p } is a member of a consensus cluster @{term C} and @{term Q} is a quorum of a member of @{term C}, then @{term "Q\<inter>W"}
 must block @{term p}, as otherwise quorum intersection would be violated. \<close>

inductive not_blocked for p R where
  "\<lbrakk>Sl \<in> slices p; \<forall> q \<in> Sl\<inter>W . q \<notin> R \<and> \<not>blocking_min R q; q \<in> Sl\<rbrakk> \<Longrightarrow> not_blocked p R q"
| "\<lbrakk>not_blocked p R p'; p' \<in> W; Sl \<in> slices p'; \<forall> q \<in> Sl\<inter>W . q \<notin> R \<and> \<not>blocking_min R q; q \<in> Sl\<rbrakk> \<Longrightarrow> not_blocked p R q"
inductive_cases not_blocked_cases:"not_blocked p R q"

lemma l4:
  fixes Q p R
  defines "Q \<equiv> {q . not_blocked p R q}"
  shows "quorum Q"
proof -
  have "\<exists> S \<in> slices n . S \<subseteq> Q" if "n\<in>Q\<inter>W" for n
  proof-
    have "not_blocked p R n" using assms that by blast
    hence "n \<notin> R" and "\<not>blocking_min R n" by (metis Int_iff not_blocked.simps that)+
    thus ?thesis  using blocking_min.intros not_blocked.intros(2) that unfolding Q_def 
      by (simp; metis mem_Collect_eq subsetI)
  qed
  thus ?thesis by (simp add: quorum_def)
qed


lemma l5:
  fixes Q p R
  defines "Q \<equiv> {q . not_blocked p R q}"
  assumes  "\<not>blocking_min R p" and \<open>p\<in>C\<close> and \<open>is_cons_cluster C\<close>
  shows "quorum_of p Q" 
proof -
  have "p\<in>W"
    using assms(3,4) cons_cluster_wb by blast 
  obtain Sl where "Sl \<in> slices p" and "\<forall> q \<in> Sl\<inter>W . q \<notin> R \<and> \<not>blocking_min R q"
    by (meson \<open>p \<in> W\<close> assms(2) blocking_min.intros)
  hence "Sl \<subseteq> Q" unfolding Q_def using not_blocked.intros(1) by blast
  with l4 \<open>Sl \<in> slices p\<close> show "quorum_of p Q"
    using Q_def  quorum_of_def by blast
qed

lemma cons_cluster_ne_slices:
  assumes "is_cons_cluster C" and "p\<in>C" and "Sl \<in> slices p"
  shows "Sl\<noteq>{}"
  using assms cons_cluster_has_ne_slices cons_cluster_wb stellar.quorum_of_def stellar_axioms by fastforce

lemma l6:
  fixes Q p R
  defines "Q \<equiv> {q . not_blocked p R q}"
  shows "Q \<inter> R \<inter> W = {}"
proof -
  have "q \<notin> R" if "not_blocked p R q" and "q\<in> W" for q using that
    by (metis Int_iff not_blocked.simps)
  thus ?thesis unfolding Q_def by auto
qed

theorem quorum_blocks_cons_cluster:
  assumes "quorum_of_set C Q" and "p\<in>C" and "is_cons_cluster C"
  shows "blocking_min (Q \<inter> W) p"
proof (rule ccontr) 
  assume "\<not> blocking_min (Q \<inter> W) p"
  have "p\<in>W" using assms(2,3) is_cons_cluster_def by auto 
  define Q' where "Q' \<equiv> {q . not_blocked p (Q\<inter>W) q}"
  have "quorum_of p Q'" using Q'_def \<open>\<not> blocking_min (Q \<inter> W) p\<close> assms(2) assms(3) l5(1) by blast
  moreover have "Q' \<inter> Q \<inter> W = {}"
    using Q'_def l6 by fastforce
  ultimately show False using assms unfolding is_cons_cluster_def
    by (metis Int_commute inf_sup_aci(2) quorum_of_set_def) 
qed

subsection \<open>Reachability through a set\<close>

text \<open>Here we define the part of a quorum @{term Q} of @{term p} that is reachable through correct
participants from @{term p}. We show that if @{term p} and @{term p'} are members of the same consensus cluster and @{term Q} is a quorum of @{term p}
 and @{term Q'} is a quorum of @{term p'},
then the intersection @{term "Q\<inter>Q'\<inter>W"} is reachable from both @{term p} and @{term p'} through the consensus cluster.\<close>

inductive reachable_through for p S where
  "reachable_through p S p"
| "\<lbrakk>reachable_through p S p'; p' \<in> W; Sl \<in> slices p'; Sl \<subseteq> S; p'' \<in> Sl\<rbrakk> \<Longrightarrow> reachable_through p S p''"

definition truncation where "truncation p S \<equiv> {p' . reachable_through p S p'}"

lemma l13:
  assumes "quorum_of p Q" and "p \<in> W" and "reachable_through p Q p'"
  shows "quorum_of p' Q"
  using assms using quorum_assm reachable_through.cases
  by (metis is_pbqs subset_iff)

lemma l14:
  assumes "quorum_of p Q" and "p \<in> W"
  shows "quorum (truncation p Q)"
proof -
  have "\<exists> S \<in> slices p' . \<forall> q \<in> S . reachable_through p Q q" if "reachable_through p Q p'" and "p' \<in> W" for p'
    by (meson assms l13 quorum_is_quorum_of_some_slice stellar.reachable_through.intros(2) stellar_axioms that)
  thus ?thesis
    by (metis IntE mem_Collect_eq stellar.quorum_def stellar_axioms subsetI truncation_def)  
qed

lemma l15:
  assumes "is_cons_cluster I" and "quorum_of p Q" and "quorum_of p' Q'" and "p \<in> I" and "p' \<in> I" and "Q \<inter> Q' \<inter> W \<noteq> {}"
  shows "W \<inter> (truncation p Q) \<inter> (truncation p' Q') \<noteq> {}" 
proof -
  have "quorum (truncation p Q)" and "quorum (truncation p' Q')" using l14 assms is_cons_cluster_def by auto
  moreover have "quorum_of_set I (truncation p Q)" and "quorum_of_set I (truncation p' Q')"
    by (metis IntI assms(4,5) calculation mem_Collect_eq quorum_def quorum_of_def quorum_of_set_def reachable_through.intros(1) truncation_def)+
  moreover note \<open>is_cons_cluster I\<close>
  ultimately show ?thesis unfolding is_cons_cluster_def by auto
qed

end

subsection "Elementary quorums"

text \<open>In this section we define the notion of elementary quorum, which is a quorum that has no strict subset that is a quorum.
  It follows directly from the definition that every finite quorum contains an elementary quorum. Moreover, we show 
that if @{term Q} is an elementary quorum and @{term n\<^sub>1} and @{term n\<^sub>2} are members of @{term Q}, then @{term n\<^sub>2} is reachable from @{term n\<^sub>1} 
in the directed graph over participants defined as the set of edges @{term "(n,m)"} such that @{term m} is a member of a slice of @{term n}.
This lemma is used in the companion paper to show that probabilistic leader-election is feasible.\<close>

locale elementary = stellar
begin 

definition elementary where
  "elementary s \<equiv> quorum s \<and> (\<forall> s' . s' \<subset> s \<longrightarrow> \<not>quorum s')"

lemma finite_subset_wf:
  shows "wf {(X, Y). X \<subset> Y \<and> finite Y}"
  by (metis finite_psubset_def wf_finite_psubset)

lemma quorum_contains_elementary:
  assumes "finite s" and  "\<not> elementary s" and "quorum s" 
  shows "\<exists> s' . s' \<subset> s \<and> elementary s'" using assms
proof (induct s rule:wf_induct[where ?r="{(X, Y). X \<subset> Y \<and> finite Y}"])
  case 1
  then show ?case using finite_subset_wf by simp
next
  case (2 x)
  then show ?case
    by (metis (full_types) elementary_def finite_psubset_def finite_subset in_finite_psubset less_le psubset_trans)
qed

inductive path where
  "path []"
| "\<And> x . path [x]"
| "\<And> l n . \<lbrakk>path l; S \<in> Q (hd l); n \<in> S\<rbrakk> \<Longrightarrow> path (n#l)"

theorem elementary_connected:
  assumes "elementary s" and "n\<^sub>1 \<in> s" and "n\<^sub>2 \<in> s" and "n\<^sub>1 \<in> W" and "n\<^sub>2 \<in> W"
  shows "\<exists> l . hd (rev l) = n\<^sub>1 \<and> hd l = n\<^sub>2 \<and> path l" (is ?P)
proof -
  { assume "\<not>?P"
    define x where "x \<equiv> {n \<in> s . \<exists> l . l \<noteq> [] \<and> hd (rev l) = n\<^sub>1 \<and> hd l = n \<and> path l}"
    have "n\<^sub>2 \<notin> x" using \<open>\<not>?P\<close> x_def by auto 
    have "n\<^sub>1 \<in> x" unfolding x_def using assms(2) path.intros(2) by force
    have "quorum x"
    proof -
      { fix n
        assume "n \<in> x"
        have "\<exists> S . S \<in> slices n \<and> S \<subseteq> x"
        proof -
          obtain S where "S \<in> slices n" and "S \<subseteq> s" using \<open>elementary s\<close> \<open>n \<in> x\<close> unfolding x_def
            by (force simp add:elementary_def quorum_def)
          have "S \<subseteq> x"
          proof -
            { assume "\<not> S \<subseteq> x"
              obtain m where "m \<in> S" and "m \<notin> x" using \<open>\<not> S \<subseteq> x\<close> by auto
              obtain l' where "hd (rev l') = n\<^sub>1" and "hd l' = n" and "path l'" and "l' \<noteq> []"
                using \<open>n \<in> x\<close> x_def by blast 
              have "path (m # l')" using \<open>path l'\<close> \<open>m\<in> S\<close> \<open>S \<in> slices n\<close> \<open>hd l' = n\<close>
                using path.intros(3) by fastforce
              moreover have "hd (rev (m # l')) = n\<^sub>1" using \<open>hd (rev l') = n\<^sub>1\<close> \<open>l' \<noteq> []\<close> by auto
              ultimately have "m \<in> x" using \<open>m \<in> S\<close> \<open>S \<subseteq> s\<close> x_def by auto 
              hence False using \<open>m \<notin> x\<close> by blast }
            thus ?thesis by blast
          qed
          thus ?thesis
            using \<open>S \<in> slices n\<close> by blast
        qed }
      thus ?thesis by (meson Int_iff quorum_def)
    qed 
    moreover have "x \<subset> s"
      using \<open>n\<^sub>2 \<notin> x\<close> assms(3) x_def by blast
    ultimately have False using \<open>elementary s\<close>
      using elementary_def by auto
  }
  thus ?P by blast  
qed


end

subsection \<open>The intact sets of the Stellar Whitepaper\<close>

definition project where 
  "project slices S n \<equiv> {Sl \<inter> S | Sl . Sl \<in> slices n}" 
  \<comment> \<open>Projecting on @{term S} is the same as deleting the complement of @{term S}, where deleting is understood as in the Stellar Whitepaper.\<close>

subsubsection \<open>Intact and the Cascade Theorem\<close>

locale intact = \<comment> \<open>Here we fix an intact set @{term I} and prove the cascade theorem.\<close>
  orig:stellar slices W 
  + proj:stellar "project slices I" W \<comment> \<open>We consider the projection of the system on @{term I}.\<close>
  for slices W I +  \<comment> \<open>An intact set is a set @{term I} satisfying the three assumptions below:\<close>
  assumes intact_wb:"I \<subseteq> W"
    and q_avail:"orig.quorum I" \<comment> \<open>@{term I} is a quorum in the original system.\<close>
    and q_inter:"\<And> Q Q' . \<lbrakk>proj.quorum Q; proj.quorum Q'; Q \<inter> I \<noteq> {}; Q' \<inter> I \<noteq> {}\<rbrakk>  \<Longrightarrow> Q \<inter> Q' \<inter> I \<noteq> {}" 
    \<comment> \<open>Any two sets that intersect @{term I} and that are quorums in the projected system intersect in @{term I}.
Note that requiring that @{text \<open>Q \<inter> Q' \<noteq> {}\<close>} instead of @{text \<open>Q \<inter> Q' \<inter> I \<noteq> {}\<close>} would be equivalent.\<close>
begin

theorem blocking_safe: \<comment> \<open>A set that blocks an intact node contains an intact node. 
If this were not the case, quorum availability would trivially be violated.\<close>
  fixes S n
  assumes "n\<in>I" and "\<forall> Sl\<in> slices n .Sl\<inter>S \<noteq> {}"
  shows "S \<inter> I \<noteq> {}"
  using assms q_avail intact_wb unfolding orig.quorum_def 
  by auto (metis inf.absorb_iff2 inf_assoc inf_bot_right inf_sup_aci(1)) 

theorem cascade:
\<comment> \<open>If @{term U} is a quorum of an intact node and @{term S} is a super-set of @{term U}, then either @{term S} includes 
all intact nodes or there is an intact node outside of @{term S} which is blocked by the intact members of @{term S}.
This shows that, in SCP, once the intact members of a quorum accept a statement, 
a cascading effect occurs and all intact nodes eventually accept it regardless of what befouled and faulty nodes do.\<close>
  fixes U S
  assumes "orig.quorum U" and "U \<inter> I \<noteq> {}" and "U \<subseteq> S"
  obtains "I \<subseteq> S" | "\<exists> n \<in> I - S . \<forall> Sl \<in> slices n . Sl \<inter> S \<inter> I \<noteq> {}"
proof -
  have False if 1:"\<forall> n \<in> I - S . \<exists> Sl \<in> slices n . Sl \<inter> S \<inter> I = {}" and 2:"\<not>(I \<subseteq> S)"
  proof -
    text \<open>First we show that @{term \<open>I-S\<close>} is a quorum in the projected system. This is immediate from the definition of quorum and assumption 1.\<close>
    have "proj.quorum (I-S)" using 1
      unfolding proj.quorum_def project_def 
      by (auto; smt DiffI Diff_Compl Diff_Int_distrib Diff_eq Diff_eq_empty_iff Int_commute)
    text \<open>Then we show that U is also a quorum in the projected system:\<close>
    moreover have "proj.quorum U" using \<open>orig.quorum U\<close> 
      unfolding proj.quorum_def orig.quorum_def project_def 
      by (simp; meson Int_commute inf.coboundedI2)
    text \<open>Since quorums of @{term I} must intersect, we get a contradiction:\<close>
    ultimately show False using \<open>U \<subseteq> S\<close> \<open>U \<inter> I \<noteq> {}\<close> \<open>\<not>(I\<subseteq>S)\<close> q_inter by auto
  qed
  thus ?thesis using that by blast
qed

end

subsubsection "The Union Theorem"

text \<open>Here we prove that the union of two intact sets that intersect is intact.
This implies that maximal intact sets are disjoint.\<close>

locale intersecting_intact = 
  i1:intact slices W I\<^sub>1 + i2:intact slices W I\<^sub>2 \<comment> \<open>We fix two intersecting intact sets @{term I\<^sub>1} and @{term I\<^sub>2}.\<close>
  + proj:stellar "project slices (I\<^sub>1\<union>I\<^sub>2)" W \<comment> \<open>We consider the projection of the system on @{term \<open>I\<^sub>1\<union>I\<^sub>2\<close>}.\<close>
  for slices W I\<^sub>1 I\<^sub>2 +
assumes inter:"I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}"
begin

theorem union_quorum: "i1.orig.quorum (I\<^sub>1\<union>I\<^sub>2)" \<comment> \<open>@{term \<open>I\<^sub>1\<union>I\<^sub>2\<close>} is a quorum in the original system.\<close>
  using i1.intact_axioms i2.intact_axioms
  unfolding  intact_def stellar_def intact_axioms_def i1.orig.quorum_def
  by (metis Int_iff Un_iff le_supI1 le_supI2)

theorem union_quorum_intersection: 
  assumes "proj.quorum Q\<^sub>1" and "proj.quorum Q\<^sub>2" and "Q\<^sub>1 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}" and "Q\<^sub>2 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}"
  shows "Q\<^sub>1 \<inter> Q\<^sub>2 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}"
    \<comment> \<open>Any two sets that intersect @{term \<open>I\<^sub>1\<union>I\<^sub>2\<close>} and that are quorums in the system projected on @{term \<open>I\<^sub>1\<union>I\<^sub>2\<close>} intersect in @{term \<open>I\<^sub>1\<union>I\<^sub>2\<close>}.\<close>
proof -
  text \<open>First we show that @{term Q\<^sub>1} and @{term Q\<^sub>2} are quorums in the projections on @{term I\<^sub>1} and @{term I\<^sub>2}.\<close>
  have "i1.proj.quorum Q\<^sub>1" using \<open>proj.quorum Q\<^sub>1\<close> 
    unfolding i1.proj.quorum_def proj.quorum_def project_def
    by auto (metis Int_Un_distrib Int_iff Un_subset_iff) 
  moreover have "i2.proj.quorum Q\<^sub>2" using \<open>proj.quorum Q\<^sub>2\<close> 
    unfolding i2.proj.quorum_def proj.quorum_def project_def
    by auto (metis Int_Un_distrib Int_iff Un_subset_iff) 
  moreover have "i2.proj.quorum Q\<^sub>1" using \<open>proj.quorum Q\<^sub>1\<close>
    unfolding proj.quorum_def i2.proj.quorum_def project_def
    by auto (metis Int_Un_distrib Int_iff Un_subset_iff) 
  moreover have "i1.proj.quorum Q\<^sub>2" using \<open>proj.quorum Q\<^sub>2\<close>
    unfolding proj.quorum_def i1.proj.quorum_def project_def
    by auto (metis Int_Un_distrib Int_iff Un_subset_iff) 
  text \<open>Next we show that @{term Q\<^sub>1} and @{term Q\<^sub>2} intersect if they are quorums of, respectively, @{term I\<^sub>1} and @{term I\<^sub>2}. 
This is the only interesting part of the proof.\<close> 
  moreover have "Q\<^sub>1 \<inter> Q\<^sub>2 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}" 
    if "i1.proj.quorum Q\<^sub>1" and "i2.proj.quorum Q\<^sub>2" and "i2.proj.quorum Q\<^sub>1"
      and "Q\<^sub>1 \<inter> I\<^sub>1 \<noteq> {}" and "Q\<^sub>2 \<inter> I\<^sub>2 \<noteq> {}"
    for Q\<^sub>1 Q\<^sub>2
  proof -
    have "i1.proj.quorum I\<^sub>2" 
    proof -
      have "i1.orig.quorum I\<^sub>2" by (simp add: i2.q_avail)
      thus ?thesis unfolding i1.orig.quorum_def i1.proj.quorum_def project_def
        by auto (meson Int_commute Int_iff inf_le2 subset_trans)
    qed
    moreover note \<open>i1.proj.quorum Q\<^sub>1\<close>
    ultimately have "Q\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}" using i1.q_inter inter \<open>Q\<^sub>1 \<inter> I\<^sub>1 \<noteq> {}\<close> by blast

    moreover note \<open>i2.proj.quorum Q\<^sub>2\<close>  
    moreover note \<open>i2.proj.quorum Q\<^sub>1\<close>
    ultimately have "Q\<^sub>1 \<inter> Q\<^sub>2 \<inter> I\<^sub>2 \<noteq> {}" using i2.q_inter \<open>Q\<^sub>2 \<inter> I\<^sub>2 \<noteq> {}\<close> by blast 
    thus ?thesis by (simp add: inf_sup_distrib1)
  qed
  text \<open>Next  we show that @{term Q\<^sub>1} and @{term Q\<^sub>2} intersect if they are quorums of the same intact set. This is obvious.\<close>
  moreover
  have "Q\<^sub>1 \<inter> Q\<^sub>2 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}" 
    if "i1.proj.quorum Q\<^sub>1" and "i1.proj.quorum Q\<^sub>2" and "Q\<^sub>1 \<inter> I\<^sub>1 \<noteq> {}" and "Q\<^sub>2 \<inter> I\<^sub>1 \<noteq> {}"
    for Q\<^sub>1 Q\<^sub>2
    by (simp add: Int_Un_distrib i1.q_inter that)  
  moreover
  have "Q\<^sub>1 \<inter> Q\<^sub>2 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}"
    if "i2.proj.quorum Q\<^sub>1" and "i2.proj.quorum Q\<^sub>2" and "Q\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}" and "Q\<^sub>2 \<inter> I\<^sub>2 \<noteq> {}"
    for Q\<^sub>1 Q\<^sub>2
    by (simp add: Int_Un_distrib i2.q_inter that)
  text \<open>Finally we have covered all the cases and get the final result:\<close>
  ultimately
  show ?thesis
    by (smt Int_Un_distrib Int_commute assms(3,4) sup_bot.right_neutral) 
qed

end

end
