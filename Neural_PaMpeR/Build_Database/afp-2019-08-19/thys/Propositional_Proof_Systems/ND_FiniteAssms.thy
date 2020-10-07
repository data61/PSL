theory ND_FiniteAssms
imports ND
begin

lemma ND_finite_assms: "\<Gamma> \<turnstile> F \<Longrightarrow> \<exists>\<Gamma>'. \<Gamma>' \<subseteq> \<Gamma> \<and> finite \<Gamma>' \<and> (\<Gamma>' \<turnstile> F)"
proof(induction rule: ND.induct)
  case (Ax F \<Gamma>) thus ?case by(intro exI[of _ "{F}"]) (simp add: ND.Ax)
next
  case (AndI \<Gamma> F G)
  from AndI.IH(1) guess \<Gamma>1 .. moreover
  from AndI.IH(2) guess \<Gamma>2 .. ultimately
  show ?case by(intro exI[where x="\<Gamma>1\<union>\<Gamma>2"]) (force elim: Weaken intro!: ND.AndI)
next
  case (CC F \<Gamma>)
  from CC.IH guess \<Gamma>' .. note \<Gamma>' = this
  thus ?case proof(cases "Not F \<in> \<Gamma>'") text\<open>case distinction: Did we actually use @{term "\<^bold>\<not>F"}?\<close>
    case False hence "\<Gamma>' \<subseteq> \<Gamma>" using \<Gamma>' by blast
    with \<Gamma>' show ?thesis using BotE by(intro exI[where x="\<Gamma>'"]) fast
  next
    case True
    then obtain \<Gamma>'' where "\<Gamma>' = \<^bold>\<not> F\<triangleright>\<Gamma>''" "\<^bold>\<not> F \<notin> \<Gamma>''" by (meson Set.set_insert)
    hence "\<Gamma>'' \<subseteq> \<Gamma>" "finite \<Gamma>''" "\<^bold>\<not> F\<triangleright>\<Gamma>'' \<turnstile> \<bottom>" using \<Gamma>' by auto
    thus ?thesis using ND.CC by auto
  qed
next
  case AndE1 thus ?case by(blast dest: ND.AndE1) next
  case AndE2 thus ?case by(blast dest: ND.AndE2)
next
  case OrI1 thus ?case by(blast dest: ND.OrI1) next
  case OrI2 thus ?case by(blast dest: ND.OrI2)
next
  case (OrE \<Gamma> F G H)
  from OrE.IH(1) guess \<Gamma>1 .. moreover
  from OrE.IH(2) guess \<Gamma>2 .. moreover
  from OrE.IH(3) guess \<Gamma>3 ..
  note IH = calculation this
  let ?w = "\<Gamma>1 \<union> (\<Gamma>2 - {F}) \<union> (\<Gamma>3 - {G})"
  from IH have "?w \<turnstile> F \<^bold>\<or> G" using Weaken[OF _ sup_ge1] by metis moreover
  from IH have "F\<triangleright>?w \<turnstile> H" "G\<triangleright>?w \<turnstile> H" using Weaken by (metis Un_commute Un_insert_right Un_upper1 Weaken insert_Diff_single)+ ultimately
  have "?w \<turnstile> H" using ND.OrE by blast
  thus ?case using IH by(intro exI[where x="?w"]) auto
  text\<open>Clever evasion of the case distinction made for CC.\<close>
next
  case (ImpI F \<Gamma> G)
  from ImpI.IH guess \<Gamma>' ..
  thus ?case by (intro exI[where x="\<Gamma>' - {F}"]) (force elim: Weaken intro!: ND.ImpI)
next
  case (ImpE \<Gamma> F G)
  from ImpE.IH(1) guess \<Gamma>1 .. moreover
  from ImpE.IH(2) guess \<Gamma>2 .. ultimately
  show ?case by(intro exI[where x="\<Gamma>1 \<union> \<Gamma>2"]) (force elim: Weaken intro: ND.ImpE[where F=F])
next
  case (NotE \<Gamma> F)
  from NotE.IH(1) guess \<Gamma>1 .. moreover
  from NotE.IH(2) guess \<Gamma>2 .. ultimately
  show ?case by(intro exI[where x="\<Gamma>1 \<union> \<Gamma>2"]) (force elim: Weaken intro: ND.NotE[where F=F])
next
  case (NotI F \<Gamma>)
  from NotI.IH guess \<Gamma>' ..
  thus ?case by(intro exI[where x="\<Gamma>' - {F}"]) (force elim: Weaken intro: ND.NotI[where F=F])
qed

text\<open>We thought that a lemma like this would be necessary for the ND completeness by SC completeness proof
  (this lemma shows that if we made an ND proof, we can always limit ourselves to a finite set of assumptions --
   and thus put all the assumptions into one formula).
That is not the case, since in the completeness proof,
we assume a valid entailment and have to show (the existence of) a derivation.
The author hopes that his misunderstanding can help the reader's understanding.\<close>
corollary ND_no_assms: 
  assumes "\<Gamma> \<turnstile> F"
  obtains \<Gamma>' where "set \<Gamma>' \<subseteq> \<Gamma> \<and> ({} \<turnstile> \<^bold>\<And>\<Gamma>' \<^bold>\<rightarrow> F)"
proof(goal_cases)
  case 1
  from ND_finite_assms[OF assms] obtain \<Gamma>' where "\<Gamma>'\<subseteq>\<Gamma>" "finite \<Gamma>'" "\<Gamma>' \<turnstile> F" by blast
  from \<open>finite \<Gamma>'\<close> obtain G where \<Gamma>'[simp]: "\<Gamma>' = set G"  using finite_list by blast
  with \<open>\<Gamma>'\<subseteq>\<Gamma>\<close> have "set G \<subseteq> \<Gamma>" by clarify
  moreover from \<open>\<Gamma>' \<turnstile> F\<close> have "{} \<turnstile> \<^bold>\<And> G \<^bold>\<rightarrow> F" unfolding \<Gamma>' AssmBigAnd .
  ultimately show ?case by(intro 1[where \<Gamma>'=G] conjI)
qed

end
