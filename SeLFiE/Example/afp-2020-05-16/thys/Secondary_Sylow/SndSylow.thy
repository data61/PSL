(*  Title:      Secondary Sylow Theorems
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer at student.kit.edu>
*)

theory SndSylow
imports SubgroupConjugation
begin

no_notation Multiset.subset_mset  (infix "<#" 50) (*prevent a clash with the same syntax for l_coset*)

section \<open>The Secondary Sylow Theorems\<close>

subsection \<open>Preliminaries\<close>

lemma singletonI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> x = y"
  assumes "y \<in> A"
  shows "A = {y}"
using assms by fastforce

context group
begin

lemma set_mult_inclusion:
  assumes H:"subgroup H G"
  assumes Q:"P \<subseteq> carrier G"
  assumes PQ:"H <#> P \<subseteq> H"
  shows "P \<subseteq> H"
proof
  fix x
  from H have "\<one> \<in> H" by (rule subgroup.one_closed)
  moreover assume x:"x \<in> P"
  ultimately have "\<one> \<otimes> x \<in> H <#> P" unfolding set_mult_def by auto
  with PQ have "\<one> \<otimes> x \<in> H" by auto
  with H Q x show  "x \<in> H" by (metis in_mono l_one)
qed

lemma card_subgrp_dvd:
  assumes "subgroup H G"
  shows "card H dvd order G"
proof(cases "finite (carrier G)")
  case True
  with assms have "card (rcosets H) * card H = order G" by (metis lagrange)
  thus ?thesis by (metis dvd_triv_left mult.commute)
next
  case False
  hence "order G = 0" unfolding order_def by (metis card_infinite)
  thus ?thesis by (metis dvd_0_right)
qed

lemma subgroup_finite:
  assumes subgroup:"subgroup H G"
  assumes finite:"finite (carrier G)"
  shows "finite H"
by (metis finite finite_subset subgroup subgroup.subset)

end

subsection \<open>Extending the Sylow Locale\<close>

text \<open>This locale extends the originale @{term sylow} locale by adding
the constraint that the @{term p} must not divide the remainder @{term m},
i.e. @{term "p ^ a"} is the maximal size of a @{term p}-subgroup of
@{term G}.\<close>

locale snd_sylow = sylow +
  assumes pNotDvdm:"\<not> (p dvd m)"

context snd_sylow
begin

lemma pa_not_zero: "p ^ a \<noteq> 0"
  by (simp add: prime_gt_0_nat prime_p)

lemma sylow_greater_zero:
  shows "card (subgroups_of_size (p ^ a)) > 0"
proof -
  obtain P where PG:"subgroup P G" and cardP:"card P = p ^ a" by (metis sylow_thm)
  hence "P \<in> subgroups_of_size (p ^ a)" unfolding subgroups_of_size_def by auto
  hence "subgroups_of_size (p ^ a) \<noteq> {}" by auto
  moreover from finite_G have "finite (subgroups_of_size (p ^ a))" unfolding subgroups_of_size_def subgroup_def by auto
  ultimately show ?thesis by auto
qed

lemma is_snd_sylow: "snd_sylow G p a m" by (rule snd_sylow_axioms)

subsection \<open>Every $p$-group is Contained in a conjugate of a $p$-Sylow-Group\<close>

lemma ex_conj_sylow_group:
  assumes H:"H \<in> subgroups_of_size (p ^ b)"
  assumes Psize:"P \<in> subgroups_of_size (p ^ a)"
  obtains g where "g \<in> carrier G" "H \<subseteq> g <# (P #> inv g)"
proof -
  from H have HsubG:"subgroup H G" unfolding subgroups_of_size_def by auto
  hence HG:"H \<subseteq> carrier G" unfolding subgroups_of_size_def by (simp add:subgroup.subset)
  from Psize have PG:"subgroup P G" and cardP:"card P = p ^ a" unfolding subgroups_of_size_def by auto
  define H' where "H' = G\<lparr>carrier := H\<rparr>"
  from HsubG interpret Hgroup: group H' unfolding H'_def by (metis subgroup_imp_group)
  from H have orderH':"order H' =  p ^ b" unfolding H'_def subgroups_of_size_def order_def by simp
  define \<phi> where "\<phi> = (\<lambda>g. \<lambda>U\<in>rcosets P. U #> inv g)"
  with PG interpret Gact: group_action G \<phi> "rcosets P" unfolding \<phi>_def by (metis inv_mult_on_rcosets_action)
  from H interpret H'act: group_action H' \<phi> "rcosets P" unfolding H'_def subgroups_of_size_def by (metis (mono_tags) Gact.subgroup_action mem_Collect_eq)
  from finite_G PG have "finite (rcosets P)" unfolding RCOSETS_def r_coset_def by (metis (lifting) finite.emptyI finite_UN_I finite_insert)
  with orderH' sylow_axioms cardP have "card H'act.fixed_points mod p = card (rcosets P) mod p" unfolding sylow_def sylow_axioms_def by (metis H'act.fixed_point_congruence)
  moreover from finite_G PG order_G cardP  have "card (rcosets P) * p ^ a  = p ^ a * m" by (metis lagrange)
  with prime_p have "card (rcosets P) = m" by (metis less_nat_zero_code mult_cancel2 mult_is_0 mult.commute order_G zero_less_o_G)
  hence "card (rcosets P) mod p = m mod p" by simp
  moreover from pNotDvdm prime_p have "... \<noteq> 0" by (metis dvd_eq_mod_eq_0)
  ultimately have "card H'act.fixed_points \<noteq> 0" by (metis mod_0)
  then obtain N where N:"N \<in> H'act.fixed_points" by fastforce
  hence Ncoset:"N \<in> rcosets P" unfolding H'act.fixed_points_def by simp
  then obtain g where g:"g \<in> carrier G" "N = P #> g" unfolding RCOSETS_def by auto
  hence invg:"inv g \<in> carrier G" by (metis inv_closed)
  hence invinvg:"inv (inv g) \<in> carrier G" by (metis inv_closed)
  from N have "carrier H' \<subseteq> H'act.stabilizer N" unfolding H'act.fixed_points_def by simp
  hence "\<forall>h\<in>H. \<phi> h N = N" unfolding H'act.stabilizer_def using H'_def by auto
  with HG Ncoset have a1:"\<forall>h\<in>H. N #> inv h \<subseteq> N" unfolding \<phi>_def by simp
  have "N <#> H \<subseteq> N" unfolding set_mult_def r_coset_def
  proof(auto)
    fix n h
    assume n:"n \<in> N" and h:"h \<in> H"
    with H have "inv h \<in> H" by (metis (mono_tags) mem_Collect_eq subgroup.m_inv_closed subgroups_of_size_def)
    with n HG PG a1 have "n \<otimes> inv (inv h) \<in> N" unfolding r_coset_def by auto
    with HG h show  "n \<otimes> h \<in> N" by (metis in_mono inv_inv)
  qed
  with g have "((P #> g) <#> H) #> inv g \<subseteq> (P #> g) #> inv g" unfolding r_coset_def by auto
  with PG g invg have "((P #> g) <#> H) #> inv g \<subseteq> P" by (metis coset_mult_assoc coset_mult_one r_inv subgroup.subset)
  with g HG PG invg have "P <#> (g <# H #> inv g) \<subseteq> P" by (metis lr_coset_assoc r_coset_subset_G rcos_assoc_lcos setmult_rcos_assoc subgroup.subset)
  with PG HG g invg have "g <# H #> inv g \<subseteq> P" by (metis l_coset_subset_G r_coset_subset_G set_mult_inclusion)
  with g have "(g <# H #> inv g) #> inv (inv g) \<subseteq> P #> inv (inv g)" unfolding r_coset_def by auto
  with HG g invg invinvg have "g <# H \<subseteq> P #> inv (inv g)" by (metis coset_mult_assoc coset_mult_inv2 l_coset_subset_G)
  with g have "(inv g) <# (g <# H) \<subseteq> inv g <# (P #> inv (inv g))" unfolding l_coset_def by auto
  with HG g invg invinvg have "H \<subseteq> inv g <# (P #> inv (inv g))" by (metis inv_inv lcos_m_assoc lcos_mult_one r_inv)
  with invg show thesis by (auto dest:that)
qed

subsection\<open>Every $p$-Group is Contained in a $p$-Sylow-Group\<close>

theorem sylow_contained_in_sylow_group:
  assumes H:"H \<in> subgroups_of_size (p ^ b)"
  obtains S where "H \<subseteq> S" and "S \<in> subgroups_of_size (p ^ a)"
proof -
  from H have HG:"H \<subseteq> carrier G" unfolding subgroups_of_size_def by (simp add:subgroup.subset)
  obtain P where PG:"subgroup P G" and cardP:"card P = p ^ a" by (metis sylow_thm)
  hence Psize:"P \<in> subgroups_of_size (p ^ a)" unfolding subgroups_of_size_def by simp
  with H obtain g where g:"g \<in> carrier G" "H \<subseteq> g <# (P #> inv g)" by (metis ex_conj_sylow_group)
  moreover note Psize g
  moreover with finite_G have "conjugation_action (p ^ a) g P \<in> subgroups_of_size (p ^ a)" by (metis conjugation_is_size_invariant)
  ultimately show thesis unfolding conjugation_action_def by (auto dest:that)
qed

subsection\<open>$p$-Sylow-Groups are conjugates of each other\<close>

theorem sylow_conjugate:
  assumes P:"P \<in> subgroups_of_size (p ^ a)"
  assumes Q:"Q \<in> subgroups_of_size (p ^ a)"
  obtains g where "g \<in> carrier G" "Q = g <# (P #> inv g)"
proof -
  from P have "card P = p ^ a" unfolding subgroups_of_size_def by simp
  from Q have Qcard:"card Q = p ^ a" unfolding subgroups_of_size_def by simp
  from Q P obtain g where g:"g \<in> carrier G" "Q \<subseteq> g <# (P #> inv g)" by (rule ex_conj_sylow_group)
  moreover with P finite_G have "conjugation_action (p ^ a) g P \<in> subgroups_of_size (p ^ a)" by (metis conjugation_is_size_invariant)
  moreover from g P have "conjugation_action (p ^ a) g P = g <# (P #> inv g)" unfolding conjugation_action_def by simp
  ultimately have conjSize:"g <# (P #> inv g) \<in> subgroups_of_size (p ^ a)" unfolding conjugation_action_def by simp
  with Qcard have  card:"card (g <# (P #> inv g)) = card Q"  unfolding subgroups_of_size_def by simp
  from conjSize finite_G have "finite (g <# (P #> inv g))" by (metis (mono_tags) finite_subset mem_Collect_eq subgroup.subset subgroups_of_size_def)
  with g card have "Q = g <# (P #> inv g)" by (metis card_subset_eq)
  with g show thesis by (metis that)
qed

corollary sylow_conj_orbit_rel:
  assumes P:"P \<in> subgroups_of_size (p ^ a)"
  assumes Q:"Q \<in> subgroups_of_size (p ^ a)"
  shows "(P,Q) \<in> group_action.same_orbit_rel G (conjugation_action (p ^ a)) (subgroups_of_size (p ^ a))"
unfolding group_action.same_orbit_rel_def 
proof -
  from Q P obtain g where g:"g \<in> carrier G" "P = g <# (Q #> inv g)" by (rule sylow_conjugate)
  with Q P have g':"conjugation_action (p ^ a) g Q = P" unfolding conjugation_action_def by simp
  from finite_G interpret conj: group_action G "(conjugation_action (p ^ a))" "(subgroups_of_size (p ^ a))" by (rule acts_on_subsets)
  have "conj.same_orbit_rel = {X \<in> (subgroups_of_size (p ^ a) \<times> subgroups_of_size (p ^ a)). \<exists>g \<in> carrier G. ((conjugation_action (p ^ a)) g) (snd X) = (fst X)}" by (rule conj.same_orbit_rel_def)
  with g g' P Q show ?thesis by auto
qed

subsection\<open>Counting Sylow-Groups\<close>

text \<open>The number of sylow groups is the orbit size of one of them:\<close>

theorem num_eq_card_orbit:
  assumes P:"P \<in> subgroups_of_size (p ^ a)"
  shows "subgroups_of_size (p ^ a) = group_action.orbit G (conjugation_action (p ^ a)) (subgroups_of_size (p ^ a)) P"
proof(auto)
  from finite_G interpret conj: group_action G "(conjugation_action (p ^ a))" "(subgroups_of_size (p ^ a))" by (rule acts_on_subsets)
  have "group_action.orbit G (conjugation_action (p ^ a)) (subgroups_of_size (p ^ a)) P = group_action.same_orbit_rel G (conjugation_action (p ^ a)) (subgroups_of_size (p ^ a)) `` {P}" by (rule conj.orbit_def)
  fix Q
  {
    assume Q:"Q \<in> subgroups_of_size (p ^ a)"
    from P Q obtain g where g:"g \<in> carrier G" "Q = g <# (P #> inv g) " by (rule sylow_conjugate)
    with P conj.orbit_char show "Q \<in> group_action.orbit G (conjugation_action (p ^ a)) (subgroups_of_size (p ^ a)) P"
      unfolding conjugation_action_def by auto
  } {
    assume "Q \<in> group_action.orbit G (conjugation_action (p ^ a)) (subgroups_of_size (p ^ a)) P"
    with P conj.orbit_char obtain g where g:"g \<in> carrier G" "Q = conjugation_action (p ^ a) g P" by auto
    with finite_G P show "Q \<in> subgroups_of_size (p ^ a)"  by (metis conjugation_is_size_invariant)
  }
qed

theorem num_sylow_normalizer:
  assumes Psize:"P \<in> subgroups_of_size (p ^ a)"
  shows "card (rcosets\<^bsub>G\<lparr>carrier := group_action.stabilizer G (conjugation_action (p ^ a)) P\<rparr>\<^esub> P) * p ^ a = card (group_action.stabilizer G (conjugation_action (p ^ a)) P)"
proof -
  from finite_G interpret conj: group_action G "(conjugation_action (p ^ a))" "(subgroups_of_size (p ^ a))" by (rule acts_on_subsets)
  from Psize have PG:"subgroup P G" and cardP:"card P = p ^ a" unfolding subgroups_of_size_def by auto
  with finite_G have "order G = card (conj.orbit P) * card (conj.stabilizer P)" by (metis Psize acts_on_subsets group_action.orbit_size)
  with order_G Psize have "p ^ a * m = card (subgroups_of_size (p ^ a)) * card (conj.stabilizer P)" by (metis num_eq_card_orbit)
  moreover from Psize interpret stabGroup: group "G\<lparr>carrier := conj.stabilizer P\<rparr>" by (metis conj.stabilizer_is_subgroup subgroup_imp_group)
  from finite_G Psize have PStab:"subgroup P (G\<lparr>carrier := conj.stabilizer P\<rparr>)" by (rule stabilizer_supergrp_P)
  from finite_G Psize have "finite (conj.stabilizer P)" by (metis card_infinite conj.stabilizer_is_subgroup less_nat_zero_code subgroup.finite_imp_card_positive)
  with finite_G PStab stabGroup.lagrange have "card (rcosets\<^bsub>G\<lparr>carrier := conj.stabilizer P\<rparr>\<^esub> P) * card P = order (G\<lparr>carrier := conj.stabilizer P\<rparr>)" by force
  with cardP show ?thesis unfolding order_def by auto 
qed

theorem (in snd_sylow) num_sylow_dvd_remainder:
  shows "card (subgroups_of_size (p ^ a)) dvd m"
proof -
  from finite_G interpret conj: group_action G "(conjugation_action (p ^ a))" "(subgroups_of_size (p ^ a))" by (rule acts_on_subsets)
  obtain P where PG:"subgroup P G" and cardP:"card P = p ^ a" by (metis sylow_thm)
  hence Psize:"P \<in> subgroups_of_size (p ^ a)" unfolding subgroups_of_size_def by simp
  with finite_G have "order G = card (conj.orbit P) * card (conj.stabilizer P)" by (metis Psize acts_on_subsets group_action.orbit_size)
  with order_G Psize have orderEq:"p ^ a * m = card (subgroups_of_size (p ^ a)) * card (conj.stabilizer P)" by (metis num_eq_card_orbit)
  define k where "k = card (rcosets\<^bsub>G\<lparr>carrier := conj.stabilizer P\<rparr>\<^esub> P)"
  with Psize have "k * p ^ a = card (conj.stabilizer P)" by (metis num_sylow_normalizer)
  with orderEq have "p ^ a * m = card (subgroups_of_size (p ^ a)) * p ^ a * k" by (auto simp:mult.assoc mult.commute)
  hence "p ^ a * m = p ^ a * card (subgroups_of_size (p ^ a)) * k" by auto
  then have "m = card (subgroups_of_size (p ^ a)) * k"
    using pa_not_zero by auto
  then show ?thesis ..
qed

text \<open>We can restrict this locale to refer to a subgroup of order at
least @{term "(p ^ a)"}:\<close>

lemma (in snd_sylow) restrict_locale:
  assumes subgrp:"subgroup P G"
  assumes card:"p ^ a dvd card P"
  shows "snd_sylow (G\<lparr>carrier := P\<rparr>) p a ((card P) div (p ^ a))"
proof -
  from subgrp interpret groupP: group "G\<lparr>carrier := P\<rparr>" by (metis subgroup_imp_group)
  define k where "k = (card P) div (p ^ a)"
  with card have cardP:"card P = p ^ a * k" by auto
  hence orderP:"order (G\<lparr>carrier := P\<rparr>) = p ^ a * k" unfolding order_def by simp
  from cardP subgrp order_G have "p ^ a * k dvd p ^ a * m" by (metis card_subgrp_dvd)
  hence "k dvd m"
    by (metis nat_mult_dvd_cancel_disj pa_not_zero) 
  with pNotDvdm have ndvd:"\<not> p dvd k"
    by (blast intro: dvd_trans)
  define PcalM where "PcalM = {s. s \<subseteq> carrier (G\<lparr>carrier := P\<rparr>) \<and> card s = p ^ a}"
  define PRelM where "PRelM = {(N1, N2). N1 \<in> PcalM \<and> N2 \<in> PcalM \<and> (\<exists>g\<in>carrier (G\<lparr>carrier := P\<rparr>). N1 = N2 #>\<^bsub>G\<lparr>carrier := P\<rparr>\<^esub> g)}"
  from subgrp finite_G have finite_groupP:"finite (carrier (G\<lparr>carrier := P\<rparr>))" by (auto simp:subgroup_finite)
  interpret Nsylow: snd_sylow "G\<lparr>carrier := P\<rparr>" p a k PcalM PRelM
     unfolding snd_sylow_def snd_sylow_axioms_def sylow_def sylow_axioms_def k_def
     using groupP.is_group prime_p orderP finite_groupP ndvd PcalM_def PRelM_def k_def by fastforce+
  show ?thesis using k_def by (metis Nsylow.is_snd_sylow)
qed

theorem (in snd_sylow) p_sylow_mod_p:
  shows "card (subgroups_of_size (p ^ a)) mod p = 1"
proof -
  obtain P where PG:"subgroup P G" and cardP:"card P = p ^ a" by (metis sylow_thm)
  hence orderP:"order (G\<lparr>carrier := P\<rparr>) = p ^ a" unfolding order_def by auto
  from PG have PsubG:"P \<subseteq> carrier G" by (metis subgroup.subset)
  from PG cardP have PSize:"P \<in> subgroups_of_size (p ^ a)" unfolding subgroups_of_size_def by auto
  from PG interpret groupP:group "(G\<lparr>carrier := P\<rparr>)" by (rule subgroup_imp_group)
  from cardP have PSize2:"P \<in> groupP.subgroups_of_size (p ^ a)" using groupP.subgroups_of_size_def groupP.subgroup_self by auto
  from finite_G interpret conjG: group_action G "conjugation_action (p ^ a)" "subgroups_of_size (p ^ a)" by (rule acts_on_subsets)
  from PG interpret conjP: group_action "G\<lparr>carrier := P\<rparr>" "conjugation_action (p ^ a)" "subgroups_of_size (p ^ a)" by (rule conjG.subgroup_action)
  from finite_G have "finite (subgroups_of_size (p ^ a))" unfolding subgroups_of_size_def subgroup_def by auto
  with orderP prime_p have "card (subgroups_of_size (p ^ a)) mod p = card conjP.fixed_points mod p" by (rule conjP.fixed_point_congruence)
  also have "... = 1"
  proof -
    have "\<And>Q. Q \<in> conjP.fixed_points \<Longrightarrow> Q = P"
    proof -
      fix Q
      assume Qfixed:"Q \<in> conjP.fixed_points"
      hence Qsize:"Q \<in> subgroups_of_size (p ^ a)" unfolding conjP.fixed_points_def by simp
      hence cardQ:"card Q = p ^ a" unfolding subgroups_of_size_def by simp
      \<comment> \<open>The normalizer of @{term Q} in @{term G}\<close>
      \<comment> \<open>Let's first show some basic propertiers of @{text N}\<close>
      define N where "N = conjG.stabilizer Q"
      define k where "k = (card N) div (p ^ a)"
      from N_def Qsize have NG:"subgroup N G" by (metis conjG.stabilizer_is_subgroup)
      then interpret groupN: group "G\<lparr>carrier := N\<rparr>" by (metis subgroup_imp_group)
      from Qsize N_def have QN:"subgroup Q (G\<lparr>carrier := N\<rparr>)" using stabilizer_supergrp_P by auto
      \<comment> \<open>The following proposition is used to show that $P = Q$ later\<close>
      from Qsize have NfixesQ:"\<forall>g\<in>N. conjugation_action (p ^ a) g Q = Q" unfolding N_def conjG.stabilizer_def by auto
      from Qfixed have PfixesQ:"\<forall>g\<in>P. conjugation_action (p ^ a) g Q = Q" unfolding conjP.fixed_points_def conjP.stabilizer_def by auto
      with PsubG have  "P \<subseteq> N" unfolding N_def conjG.stabilizer_def by auto
      with PG N_def Qsize have PN:"subgroup P (G\<lparr>carrier := N\<rparr>)" by (metis conjG.stabilizer_is_subgroup is_group subgroup.subgroup_of_subset)
      with cardP have "p ^ a dvd order (G\<lparr>carrier := N\<rparr>)" using groupN.card_subgrp_dvd by force
      hence "p ^ a dvd card N" unfolding order_def by simp
      with NG have smaller_sylow:"snd_sylow (G\<lparr>carrier := N\<rparr>) p a k" unfolding k_def by (rule restrict_locale)
      \<comment> \<open>Instantiate the @{term snd_sylow} Locale a second time for the normalizer of @{term Q}\<close>
      define NcalM where "NcalM = {s. s \<subseteq> carrier (G\<lparr>carrier := N\<rparr>) \<and> card s = p ^ a}"
      define NRelM where "NRelM = {(N1, N2). N1 \<in> NcalM \<and> N2 \<in> NcalM \<and> (\<exists>g\<in>carrier (G\<lparr>carrier := N\<rparr>). N1 = N2 #>\<^bsub>G\<lparr>carrier := N\<rparr>\<^esub> g)}"
      interpret Nsylow: snd_sylow "G\<lparr>carrier := N\<rparr>" p a k NcalM NRelM
        unfolding NcalM_def NRelM_def using smaller_sylow .
      \<comment> \<open>@{term P} and @{term Q} are conjugate in @{term N}:\<close>
      from cardP PN have PsizeN:"P \<in> groupN.subgroups_of_size (p ^ a)" unfolding groupN.subgroups_of_size_def by auto
      from cardQ QN have QsizeN:"Q \<in> groupN.subgroups_of_size (p ^ a)" unfolding groupN.subgroups_of_size_def by auto
      from QsizeN PsizeN obtain g where g:"g \<in> carrier (G\<lparr>carrier := N\<rparr>)" "P = g <#\<^bsub>G\<lparr>carrier := N\<rparr>\<^esub> (Q #>\<^bsub>G\<lparr>carrier := N\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := N\<rparr>\<^esub> g)" by (rule Nsylow.sylow_conjugate)
      with NG have "P = g <# (Q #> inv g)" unfolding r_coset_def l_coset_def by (auto simp:m_inv_consistent)
      with NG g Qsize have "conjugation_action (p ^ a) g Q = P" unfolding conjugation_action_def using subgroup.subset by force
      with g NfixesQ show "Q = P" by auto
    qed
    moreover from finite_G PSize have "P \<in> conjP.fixed_points" using P_fixed_point_of_P_conj by auto
    ultimately have "conjP.fixed_points = {P}" by fastforce
    hence one:"card conjP.fixed_points = 1" by (auto simp: card_Suc_eq)
    with prime_p have "card conjP.fixed_points < p" unfolding prime_nat_iff by auto
    with one show ?thesis using mod_pos_pos_trivial by auto
  qed
  finally show ?thesis.
qed

end

end
